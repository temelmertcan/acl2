(ITEMS-HAVE-LEN)
(ITEMS-HAVE-LEN-OF-NIL)
(ITEMS-HAVE-LEN-OF-CDR
 (5 1 (:DEFINITION LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(ITEMS-HAVE-LEN-OF-CONS
 (25 5 (:DEFINITION LEN))
 (10 5 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 2 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
 (5 5 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(ITEMS-HAVE-LEN-OF-UPDATE-NTH
 (94 50 (:REWRITE DEFAULT-+-2))
 (72 57 (:REWRITE DEFAULT-CDR))
 (50 50 (:REWRITE DEFAULT-+-1))
 (36 18 (:REWRITE DEFAULT-CAR))
 (30 22 (:REWRITE DEFAULT-<-2))
 (29 22 (:REWRITE DEFAULT-<-1))
 (11 8 (:REWRITE ZP-OPEN))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(ITEMS-HAVE-LEN-OF-APPEND
 (205 41 (:DEFINITION LEN))
 (148 30 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
 (82 41 (:REWRITE DEFAULT-+-2))
 (76 76 (:REWRITE DEFAULT-CDR))
 (48 48 (:REWRITE DEFAULT-CAR))
 (41 41 (:REWRITE DEFAULT-+-1))
 (36 18 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (18 18 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(ITEMS-HAVE-LEN-OF-TRUE-LIST-FIX
 (336 44 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
 (240 48 (:DEFINITION LEN))
 (108 108 (:REWRITE DEFAULT-CDR))
 (96 48 (:REWRITE DEFAULT-+-2))
 (71 71 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE DEFAULT-+-1))
 )
(ITEMS-HAVE-LEN-WHEN-NOT-CONSP)
(ITEMS-HAVE-LEN-OF-NTHCDR
 (34 10 (:REWRITE ITEMS-HAVE-LEN-WHEN-NOT-CONSP))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN
 (10 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE ITEMS-HAVE-LEN-WHEN-NOT-CONSP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN
 (109 62 (:REWRITE DEFAULT-+-2))
 (65 65 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE DEFAULT-+-1))
 (48 38 (:REWRITE DEFAULT-<-2))
 (44 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE ZP-OPEN))
 )
