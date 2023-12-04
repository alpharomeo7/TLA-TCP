-------------------------------- MODULE TCP --------------------------------
EXTENDS Naturals, Sequences

CONSTANTS total1, total2              \** number of total bytes to sent for each byte
ASSUME  /\ total1 \in Nat \ {0}
        /\ total2 \in Nat \ {0}
 
 VARIABLES S1State, S2State, Msg1N, Msg2N,
                                       Msg1ACK,Msg2ACK,
                                       Msg1FIN, Msg2FIN,
                                       S1ACK, S2ACK, 
                                       S1RA, S2RA, S1SQN, S2SQN
                                     
s1 == <<S1State, S1ACK, S1RA, S1SQN>>
s2 == <<S2State, S2ACK, S2RA, S2SQN>>
m1 == <<Msg1N, Msg1ACK, Msg1FIN>>    
m2 == <<Msg2N, Msg2ACK, Msg2FIN>>                                  
                                       
 
 Init == /\ S1State = "est"
         /\ S2State = "est"
         /\ Msg1ACK = 0
         /\ Msg2ACK = 0
         /\ Msg1N  = 0  
         /\ Msg2N = 0
         /\ S1ACK = 0
         /\ S2ACK = 0
          /\ S1RA = 0
         /\ S2RA = 0
         /\ Msg1FIN = 0 
         /\ Msg2FIN = 0
         /\ S1SQN = 0 
         /\ S2SQN = 0
         
 
 Server1ACK == /\ Msg1N' = total1
               /\ Msg1ACK' = S1ACK
               /\ Msg1FIN' = 0
               /\ UNCHANGED <<s1, s2, m2>>

 Server2ACK == /\ Msg2N'= total2
               /\ Msg2ACK' = S2ACK
               /\ Msg2FIN' = 0
               /\ UNCHANGED  <<s1, s2, m1>>
               
 Server1Read == IF Msg2ACK > 0 \/ Msg2N > 0 
               THEN 
               /\ S1ACK' = S1ACK + Msg2N
               /\ S1RA' = Msg2ACK
               /\ S1State' = S1State
               /\  UNCHANGED <<s2,m1,m2>>
               ELSE 
                UNCHANGED <<s1,s2,m1,m2>>
 
 Server2Read == IF Msg1ACK > 0 \/ Msg1N > 0 
               THEN 
               /\ S2ACK' = S2ACK +  Msg1N
               /\ S2RA' = Msg1ACK
               /\ S2State' = S2State
               /\  UNCHANGED <<s1,m1,m2>>
               ELSE 
                UNCHANGED <<s1,s2,m1,m2>>   
                
 Server1FIN == IF S1RA >= total1 
               THEN 
               /\ S1RA' = S1RA
               /\ S1State' = "finished"
               /\ S1ACK' = S1ACK
               /\ Msg1N' = 1
               /\ Msg1ACK' = S1ACK
               /\ Msg1FIN' = 1
               /\  UNCHANGED <<s2,m2>>
               ELSE 
                UNCHANGED <<s1,s2,m1,m2>>  
                
                
 Server2FIN == IF S2RA >= total1 
               THEN 
               /\ S2RA' = S2RA
               /\ S2State' = "finished"
               /\ S2ACK' = S2ACK
               /\ Msg2N' = 1
               /\ Msg2ACK' = S2ACK
               /\ Msg2FIN' = 1
               /\  UNCHANGED <<s1,m1>>
               ELSE 
                UNCHANGED <<s1,s2,m1,m2>>  
                
 Next ==  \/ Server1ACK
          \/ Server2ACK
          \/ Server1Read
          \/ Server2Read
          \/ Server1FIN
          \/ Server2FIN
          
Done == ~(S1State = "finished" \/ S2State = "finished")
=============================================================================
\* Modification History
\* Last modified Sun Dec 03 19:48:46 EST 2023 by ajayr
\* Created Sun Dec 03 15:46:40 EST 2023 by ajayr
