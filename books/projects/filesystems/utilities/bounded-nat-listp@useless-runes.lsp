(BOUNDED-NAT-LISTP)
(BOUNDED-NAT-LISTP-CORRECTNESS-1
 (25 25 (:REWRITE DEFAULT-CAR))
 (22 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(BOUNDED-NAT-LISTP-CORRECTNESS-2
 (110 86 (:REWRITE DEFAULT-CAR))
 (110 55 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (83 59 (:REWRITE DEFAULT-<-2))
 (59 59 (:REWRITE DEFAULT-<-1))
 (55 55 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (43 37 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BOUNDED-NAT-LISTP-CORRECTNESS-3
 (41 41 (:REWRITE DEFAULT-CAR))
 (30 30 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 )
(BOUNDED-NAT-LISTP-CORRECTNESS-4
 (28 28 (:REWRITE DEFAULT-CAR))
 (24 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BOUNDED-NAT-LISTP-CORRECTNESS-5
 (47 28 (:REWRITE DEFAULT-<-2))
 (34 28 (:REWRITE DEFAULT-<-1))
 (30 30 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(BOUNDED-NAT-LISTP-OF-MAKE-LIST-AC
 (31 27 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-<-1))
 (22 20 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(CAR-OF-LAST-WHEN-BOUNDED-NAT-LISTP
 (23 19 (:REWRITE DEFAULT-<-2))
 (21 17 (:REWRITE DEFAULT-CAR))
 (12 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE DEFAULT-CDR))
 )
(LOWER-BOUNDED-INTEGER-LISTP)
(LOWER-BOUNDED-INTEGER-LISTP-CORRECTNESS-2
 (94 73 (:REWRITE DEFAULT-CAR))
 (58 29 (:REWRITE DEFAULT-<-2))
 (54 27 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (41 35 (:REWRITE DEFAULT-CDR))
 (29 29 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (29 29 (:REWRITE DEFAULT-<-1))
 (27 27 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(LOWER-BOUNDED-INTEGER-LISTP-CORRECTNESS-5
 (38 19 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (26 26 (:REWRITE DEFAULT-CAR))
 (26 19 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(LOWER-BOUNDED-INTEGER-LISTP-OF-REMOVE
 (42 40 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-<-2))
 (20 19 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:REWRITE DEFAULT-<-1))
 )
