------------------------------ MODULE ptpv3 ------------------------------
EXTENDS Sequences, Naturals


CONSTANT CLOCKS  \* The set of clocks
CONSTANT CORRECTION \* The objective network delay correction
CONSTANT SYNC_AUTH_FLAG \* Flag to determine if AUTH TLV is added to Sync messages
CONSTANT ANNOUNCE_AUTH_FLAG \* Flag to determine if AUTH TLV is added to Announce messages
CONSTANT TAMPER_DELTA \* Delta by which a malicious clock is tampering
CONSTANT MAX_ITERATIONS \* Max runs to avoid state explosion
ASSUME CORRECTION \in Nat
ASSUME SYNC_AUTH_FLAG \in BOOLEAN
ASSUME ANNOUNCE_AUTH_FLAG \in BOOLEAN

VARIABLES
  cState,       \* cState[c] is the state of clock c.
  cSynched,    \* The set of clocks that are synched
  cMaster,    \* The set of clocks that are master                
  msgs,         \* message queue.
  timestamp, \* message timestamp ground truth for the message currently in the queue
  source, \* message source ground truth for the message currently in the queue
  drop_once, \* flag to limit the number of times a paquet can be dropped
  replay_msg, \* message to be replayed
  sequence \* message sequence number ground truth

 
ICV_function(seq1,seq2,t1,t2,s1,s2)==
    IF seq1 = seq2 /\ t1 = t2 /\ s1 = s2 THEN
        TRUE
    ELSE 
        FALSE
        

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.                                     *)
  (*************************************************************************)
  [type : {"Sync"}, clock : CLOCKS, processed : SUBSET CLOCKS, seq_no: Nat, time_stamp: Nat, corr : Nat, source: CLOCKS, ICV: BOOLEAN, auth : BOOLEAN] \cup  [type : {"Announce"}, clock : CLOCKS, processed : SUBSET CLOCKS, seq_no: Nat, time_stamp: Nat, corr : Nat, source: CLOCKS, ICV: BOOLEAN, auth : BOOLEAN]
   
TypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ cState \in [CLOCKS -> {"init", "master", "slave"}]
  /\ cSynched \subseteq CLOCKS
  /\ cMaster \subseteq CLOCKS
  /\ msgs \subseteq Messages
  /\ timestamp \in Nat
  /\ source \subseteq CLOCKS
  /\ drop_once \in BOOLEAN
  /\ replay_msg \subseteq Messages
  /\ sequence \in Nat
  
OnlyOneMaster ==
  (*************************************************************************)
  (* The invariant ensuring there is only 1 master clock                   *)
  (*************************************************************************)
  /\(\A x, y \in cMaster : x = y)

OnlyOneMsgAtaTime ==
  (*************************************************************************)
  (* The invariant ensuring there is at most 1 message in the message queue*)
  (*************************************************************************)
  /\(\A x, y \in msgs : x = y)  
  /\(\A x, y \in source : x = y) 
  
MasterIsNotMalicious ==
  (*************************************************************************)
  (* The invariant checking that malicious clock is not the master         *)
  (*************************************************************************)
  /\ "malicious" \notin cMaster
  
ICV_OK ==
  (*************************************************************************)
  (* The invariant stating that a processing a message that has a bad ICV  *)
  (* on at least one slave is not allowed                                  *)
  (*************************************************************************)
  \/ msgs = {}
  \/\A m \in msgs : m.processed \ source # {}  => (m.auth = FALSE \/ m.ICV = TRUE)

Sync_OK ==
  (*************************************************************************)
  (* The invariant checking for the integrity of the time calculation      *)
  (*************************************************************************)
  \/ msgs = {}
  \/ \A m \in msgs : m.processed \ source # {} => (m.time_stamp + m.corr = timestamp + CORRECTION)

Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ cState = [clock \in CLOCKS |-> "init"]
  /\ cSynched   = {}
  /\ msgs = {}
  /\ cMaster = {}
  /\ timestamp = 0
  /\ source = {}  
  /\ drop_once = FALSE
  /\ replay_msg = {}
  /\ sequence = 0

(***************************************************************************)
(* Actions that may be performed by the processes                          *)
(***************************************************************************)  
Terminated ==
  (*************************************************************************)
  (*Reach a state where all clocks are synched after at least 2 cycles     *)
  (*passed                                                                 *)
  (*************************************************************************)
  /\ cSynched = CLOCKS
  /\ UNCHANGED <<cState, cMaster, cSynched, msgs, timestamp, source, drop_once, replay_msg, sequence>>
  /\ timestamp >=2
    
CLOCKSAnnounce(c) ==
  (*************************************************************************)
  (*If a clock is in "init" phase, it will broadcast its announce message  *)
  (*************************************************************************)
  /\ cState[c] = "init"
  /\ cMaster = {}
  /\ msgs = {}
  /\ msgs' = msgs \cup {[type |-> "Announce", clock |-> c, processed |-> {c}, seq_no |-> sequence+1, time_stamp|-> timestamp, corr |-> CORRECTION, source|-> c, ICV |-> ICV_function(sequence, sequence, timestamp,timestamp,c, c),auth |-> ANNOUNCE_AUTH_FLAG]}
  /\ cSynched' = cSynched \cup {c}
  /\ cMaster' = cMaster \cup {c}
  /\ cState' = [cState EXCEPT ![c] = "master"]
  /\ source' = source \cup {c}
  /\ sequence' = sequence+1
  /\ UNCHANGED <<timestamp, drop_once, replay_msg>>
  
CLOCKStoSlave(c) ==
  (*************************************************************************)
  (*If a clock is in "init" phase, but a master exists and an announce     *)
  (*message is in the queue, set itself to slave                           *)
  (*************************************************************************)
  /\ cState[c] = "init"
  /\ \E m \in msgs : (m.type = "Announce" /\ c \notin m.processed /\ (m.auth = FALSE \/ m.ICV = TRUE))
  /\ cMaster # {}
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN msgs' = {[type |-> m.type, clock |-> m.clock, processed |-> m.processed \cup {c}, seq_no |-> m.seq_no, time_stamp|-> m.time_stamp, corr |-> CORRECTION, source|-> m.source, ICV |-> m.ICV, auth |-> m.auth]}
  /\ cState' = [cState EXCEPT ![c] = "slave"]
  /\ UNCHANGED <<cMaster, cSynched, timestamp, source, drop_once, replay_msg, sequence>>
  
CLOCKSSync(c) ==
  (*************************************************************************)
  (*If a clock is in "master" phase, it will broadcast its sync message if *)
  (*msg queue empty                                                        *)
  (*************************************************************************)
  /\ cState[c] = "master"  
  /\ msgs = {}
  /\ msgs' = msgs \cup {[type |-> "Sync", clock |-> c, processed |-> {c}, seq_no |-> sequence+1, time_stamp|-> timestamp, corr |-> CORRECTION, source|-> c, ICV |-> ICV_function(sequence,sequence, timestamp,timestamp, c, c), auth |-> SYNC_AUTH_FLAG]}
  /\ source' = source \cup {c}
  /\ sequence' = sequence+1
  /\ UNCHANGED <<cMaster, cSynched, cState, timestamp, drop_once, replay_msg>>
  
CLOCKSRcvSync(c) ==
  (*************************************************************************)
  (*Clock in slave state receives sync message from master and syncs itself*)
  (*************************************************************************)
  /\ cState[c] = "slave"
  /\ \E m \in msgs: (m.type = "Sync" /\ c \notin m.processed /\ m.seq_no >= sequence /\ (m.auth = FALSE \/ m.ICV = TRUE))
  /\ cSynched' = cSynched \cup {c}
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN msgs' = {[type |-> m.type, clock |-> m.clock, processed |-> m.processed \cup {c}, seq_no |-> m.seq_no, time_stamp|-> m.time_stamp, corr |-> m.corr, source|-> m.source, ICV |-> m.ICV, auth |-> m.auth]}
  /\ UNCHANGED <<cMaster, cState, source, timestamp, drop_once, replay_msg, sequence>> 
  
ProcessMsgQueue == 
  (*************************************************************************)
  (*if a msg was received by all slave clocks, remove it from the queue    *)
  (*************************************************************************) 
  /\ (\A m \in msgs : m.processed = CLOCKS \/ ~(m.seq_no >= sequence /\ (m.auth = FALSE \/ m.ICV = TRUE)))
  /\ timestamp < MAX_ITERATIONS 
  /\ msgs # {}
  /\ msgs' = {}
  /\ source' = {}
  /\ timestamp' = timestamp + 1
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN
     IF m.type = "Sync" /\ replay_msg ={} THEN
     replay_msg' = replay_msg \cup {[type |-> "Sync", clock |-> m.clock, processed |-> {m.source}, seq_no |-> m.seq_no, time_stamp|-> m.time_stamp, corr |-> m.corr, source|-> m.source, ICV |-> m.ICV, auth |-> m.auth]}
     ELSE
     replay_msg'= replay_msg
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN
     IF (m.seq_no >= sequence /\ (m.auth = FALSE \/ m.ICV = TRUE)) THEN
     cSynched'=cSynched
     ELSE
     cSynched'=cMaster  
  /\ UNCHANGED <<cMaster, cState, drop_once, sequence>>
  
Tamper_source(c) == 
  (*************************************************************************)
  (*if a clock is named temper_source, it can tamper the message source    *)
  (*************************************************************************) 
  /\ msgs # {}
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source))
  /\ c = "tamper_source"
  /\ c \notin cMaster
  /\ (\A m \in msgs : m.source # c)
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN msgs' = {[type |-> m.type, clock |-> m.clock, processed |-> m.processed, seq_no |-> m.seq_no, time_stamp|-> m.time_stamp, corr |-> CORRECTION, source|-> c, ICV |-> ICV_function(m.seq_no,m.seq_no, m.time_stamp,m.time_stamp, m.source, c),auth |-> m.auth]}
  /\ UNCHANGED <<cMaster, cSynched, cState, source, timestamp, drop_once, replay_msg, sequence>>
  
Tamper_timestamp(c) == 
  (*************************************************************************)
  (*if a clock is named temper_timestamp, it can tamper the message        *)
  (*timestamp or sync messages                                             *)
  (*************************************************************************) 
  /\ msgs # {}
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source))
  /\ \E m \in msgs: (m.type = "Sync")
  /\ c = "tamper_timestamp"
  /\ c \notin cMaster
  /\ (\A m \in msgs : m.time_stamp = timestamp)
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN msgs' = {[type |-> m.type, clock |-> m.clock, processed |-> m.processed, seq_no |-> m.seq_no, time_stamp|-> m.time_stamp+TAMPER_DELTA, corr |-> CORRECTION , source|-> m.source, ICV |-> ICV_function(m.seq_no, m.seq_no,m.time_stamp+TAMPER_DELTA,m.time_stamp, m.source, m.source), auth |-> m.auth]}
  /\ UNCHANGED <<cMaster, cSynched, cState, source, timestamp, drop_once, replay_msg, sequence>>
  
Tamper_seq_no(c) == 
  (*************************************************************************)
  (*if a clock is named temper_seq_no it can tamper the message sequence   *)
  (* number                                                                *)
  (*************************************************************************) 
  /\ msgs # {}
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source))
  /\ c = "tamper_seq_no"
  /\ c \notin cMaster
  /\ (\A m \in msgs : m.seq_no = sequence)
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source) )
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN msgs' = {[type |-> m.type, clock |-> m.clock, processed |-> m.processed, seq_no |-> m.seq_no+TAMPER_DELTA, time_stamp|-> m.time_stamp, corr |-> CORRECTION , source|-> m.source, ICV |-> ICV_function(m.seq_no, m.seq_no+TAMPER_DELTA,m.time_stamp,m.time_stamp, m.source, m.source), auth |-> m.auth]}
  /\ UNCHANGED <<cMaster, cSynched, cState, source, timestamp, drop_once, replay_msg, sequence>>
  
Tamper_corr(c) == 
  (*************************************************************************)
  (*if a clock is temper_corr, it can tamper the message correction field  *)
  (*************************************************************************) 
  /\ msgs # {}
  /\ c = "tamper_corr"
  /\ \E m \in msgs: (m.type = "Sync")
  /\ c \notin cMaster
  /\ (\A m \in msgs : m.corr = CORRECTION)
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source))
  /\ LET m == CHOOSE x \in msgs : TRUE
     IN msgs' = {[type |-> m.type, clock |-> m.clock, processed |-> m.processed, seq_no |-> m.seq_no, time_stamp|-> m.time_stamp, corr |-> TAMPER_DELTA , source|-> m.source, ICV |-> ICV_function(m.seq_no, m.seq_no, m.time_stamp,m.time_stamp, m.source, m.source), auth |-> m.auth]}
  /\ UNCHANGED <<cMaster, cSynched, cState, source, timestamp, drop_once, replay_msg, sequence>>
    
Tamper_drop(c) == 
  (*************************************************************************)
  (*if a clock has the ability to drop messages, it can clear the message  *)
  (*from the queue before it is processed and desynch the slave clocks     *)
  (*desynching resets the sequence counter                                 *)  
  (*************************************************************************) 
  /\ msgs # {}
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source))
  /\ c = "tamper_drop"
  /\ c \notin cMaster
  /\ timestamp < MAX_ITERATIONS
  /\ cSynched' = cMaster
  /\ msgs' = {}
  /\ source' = {}
  /\ timestamp' = timestamp
  /\ sequence' = 0
  /\ UNCHANGED <<cMaster, cState, drop_once, replay_msg>>
  
Tamper_drop_once(c) == 
  (*************************************************************************)
  (*if a clock has the ability to drop messages, it can clear the message  *)
  (*from the queue before it is processed and desynch the slave clocks     *)
  (*desynching resets the sequence counter                                 *)   
  (*************************************************************************) 
  /\ msgs # {}
  /\ drop_once # TRUE
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source) )
  /\ (c = "tamper_drop_once" \/ c = "tamper_replay")
  /\ c \notin cMaster
  /\ cSynched' = cMaster
  /\ msgs' = {}
  /\ source' = {}
  /\ timestamp' = timestamp
  /\ sequence' = 0
  /\ drop_once' = TRUE
  /\ UNCHANGED <<cMaster, cState, replay_msg>>


Tamper_delay(c) == 
  (*************************************************************************)
  (*if a clock has the ability to delay messages, it can hold sync messages*)
  (*until a time unit elapses                                              *)  
  (*************************************************************************) 
  /\ msgs # {}
  /\ \E m \in msgs: (m.type = "Sync")
  /\ (\A m \in msgs : (\A item \in m.processed : item = m.source))
  /\ c = "tamper_delay"
  /\ c \notin cMaster
  /\ timestamp' = timestamp +1
  /\ UNCHANGED <<cMaster, cSynched, cState, msgs, source, drop_once, replay_msg, sequence>>

Replay(c) == 
  (*************************************************************************)
  (*if a clock has the ability to replay messages, it can replay messages  *)
  (*if a clock is unsynched and queue is empty                             *)  
  (*************************************************************************) 
  /\ msgs = {}
  /\ replay_msg # {}
  /\ cSynched # CLOCKS
  /\ c = "tamper_replay"
  /\ c \notin cMaster
  /\ LET m == CHOOSE x \in replay_msg : TRUE
     IN msgs' = msgs \cup {m}
  /\ replay_msg' = {}
  /\ source' = {c}
  /\ UNCHANGED <<cMaster, cSynched, cState, timestamp, drop_once, sequence>>

Next ==
  (*************************************************************************)
  (*next step is any possible previous step                                *)
  (*************************************************************************)
  \/ ProcessMsgQueue 
  \/ Terminated 
  \/ \E c \in CLOCKS : 
       CLOCKSAnnounce(c) \/ CLOCKSSync(c) \/ CLOCKSRcvSync(c)  \/ CLOCKStoSlave(c) \/ Tamper_source(c) \/ Tamper_timestamp(c) \/ Tamper_seq_no(c) \/ Tamper_corr(c)  \/ Tamper_drop(c) \/ Tamper_drop_once(c)  \/ Tamper_delay(c) \/ Replay(c)

(***************************************************************************)
(* Spec defining the state machine and end condition temporal properties   *)
(***************************************************************************)  
vars == << cState, cSynched,cMaster, msgs, source, timestamp, drop_once, replay_msg>>
Spec == Init /\ [][Next]_vars
End_sync == <>[][Terminated]_vars
=============================================================================
\* Modification History
\* Last modified Thu Nov 27 13:46:39 EST 2025 by tla
\* Created Thu Oct 30 16:40:05 EDT 2025 by tla
