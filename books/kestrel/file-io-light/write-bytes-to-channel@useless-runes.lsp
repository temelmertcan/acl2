(ALL-BYTEP)
(WRITE-BYTES-TO-CHANNEL
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(OPEN-OUTPUT-CHANNEL-P1-OF-WRITE-BYTES-TO-CHANNEL
 (43 14 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (29 7 (:DEFINITION STATE-P))
 (14 14 (:TYPE-PRESCRIPTION STATE-P))
 (14 14 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(STATE-P1-OF-WRITE-BYTES-TO-CHANNEL
 (14 14 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
