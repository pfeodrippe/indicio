--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS TLCExt, Naturals, Sequences, FiniteSets, TLC

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

NotifyOther(t) == 
          LET S == IF t \in Producers THEN waitSet \ Producers ELSE waitSet \ Consumers
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin waitSet
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(t)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
/\ t \notin waitSet
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(t)
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \in SUBSET (Producers \cup Consumers)

(* No Deadlock *)
Invariant == (waitSet # (Producers \cup Consumers)) /\ (TLCGet("level") < 10)

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

PutEnabled == \A p \in Producers : ENABLED Put(p, p)

FairSpec == Spec /\ WF_vars(Next) 
                 /\ \A p \in Producers : WF_vars(Put(p, p)) 

(* All producers will continuously be serviced. For this to be violated,    *)
(* ASSUME Cardinality(Producers) > 1 has to hold (a single producer cannot  *)
(* starve itself).                                                          *)
Starvation == \A p \in Producers: []<>(<<Put(p, p)>>_vars)

=============================================================================
