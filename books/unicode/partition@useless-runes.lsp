(PARTITION
 (2 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:DEFINITION TRUE-LISTP))
 )
(PARTITION-WHEN-NOT-CONSP)
(PARTITION-OF-CONS
 (255 10 (:REWRITE TAKE-OF-LEN-FREE))
 (195 5 (:DEFINITION TAKE))
 (130 5 (:DEFINITION NTHCDR))
 (122 122 (:TYPE-PRESCRIPTION LEN))
 (110 2 (:REWRITE NTHCDR-OF-NTHCDR))
 (107 10 (:REWRITE NTHCDR-WHEN-ZP))
 (102 22 (:REWRITE ZP-OPEN))
 (68 12 (:DEFINITION LEN))
 (67 27 (:REWRITE DEFAULT-CDR))
 (56 10 (:DEFINITION NFIX))
 (52 2 (:REWRITE LEN-OF-NTHCDR))
 (47 35 (:REWRITE DEFAULT-+-2))
 (37 37 (:META CANCEL_PLUS-LESSP-CORRECT))
 (37 35 (:REWRITE DEFAULT-+-1))
 (35 35 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (34 2 (:REWRITE CONSP-OF-NTHCDR))
 (32 30 (:REWRITE DEFAULT-<-2))
 (32 30 (:REWRITE DEFAULT-<-1))
 (32 11 (:DEFINITION NOT))
 (24 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (23 7 (:REWRITE COMMUTATIVITY-OF-+))
 (20 5 (:REWRITE <-0-+-NEGATIVE-1))
 (16 8 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (14 2 (:REWRITE CAR-OF-NTHCDR))
 (13 13 (:TYPE-PRESCRIPTION ZP))
 (12 2 (:DEFINITION NTH))
 (11 11 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE NTHCDR-WHEN-ATOM))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 2 (:REWRITE <-+-NEGATIVE-0-2))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:REWRITE PARTITION-WHEN-NOT-CONSP))
 (5 5 (:REWRITE OPEN-SMALL-NTHCDR))
 (5 5 (:REWRITE EQUAL-CONSTANT-+))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CONSP-OF-PARTITION-UNDER-IFF
 (172 2 (:DEFINITION PARTITION))
 (62 4 (:REWRITE TAKE-OF-LEN-FREE))
 (58 8 (:REWRITE ZP-OPEN))
 (58 2 (:DEFINITION TAKE))
 (56 2 (:DEFINITION NTHCDR))
 (50 4 (:REWRITE NTHCDR-WHEN-ZP))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (20 4 (:DEFINITION LEN))
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (14 10 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE PARTITION-WHEN-NOT-CONSP))
 (4 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
 (2 2 (:REWRITE EQUAL-CONSTANT-+))
 )
(SUM-LIST-WHEN-NAT-LISTP-AND-Z-LISTP
 (16 16 (:REWRITE SUM-LIST-WHEN-NOT-CONSP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (5 5 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE Z-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(REASSEMBLE-LEMMA
 (370 26 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (264 113 (:REWRITE DEFAULT-CDR))
 (199 28 (:DEFINITION TRUE-LISTP))
 (189 13 (:REWRITE TAKE-OF-LEN-FREE))
 (159 95 (:REWRITE DEFAULT-+-2))
 (159 7 (:REWRITE CONSP-OF-NTHCDR))
 (132 132 (:META CANCEL_PLUS-LESSP-CORRECT))
 (123 24 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (114 95 (:REWRITE DEFAULT-<-1))
 (103 95 (:REWRITE DEFAULT-<-2))
 (102 95 (:REWRITE DEFAULT-+-1))
 (90 3 (:REWRITE TRUE-LISTP-OF-NTHCDR))
 (81 3 (:REWRITE LEN-OF-NTHCDR))
 (38 38 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (38 38 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (18 18 (:REWRITE NTHCDR-WHEN-ATOM))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (15 15 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE EQUAL-CONSTANT-+))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(FLATTEN-OF-PARTITION
 (1391 60 (:REWRITE TAKE-OF-LEN-FREE))
 (1344 13 (:REWRITE FLATTEN-WHEN-NOT-CONSP))
 (1305 13 (:REWRITE CONSP-OF-PARTITION-UNDER-IFF))
 (1228 30 (:DEFINITION TAKE))
 (868 129 (:REWRITE ZP-OPEN))
 (868 32 (:DEFINITION NTHCDR))
 (714 14 (:REWRITE NTHCDR-OF-NTHCDR))
 (707 64 (:REWRITE NTHCDR-WHEN-ZP))
 (675 127 (:DEFINITION LEN))
 (547 264 (:REWRITE DEFAULT-CDR))
 (462 310 (:REWRITE DEFAULT-+-2))
 (384 384 (:META CANCEL_PLUS-LESSP-CORRECT))
 (366 330 (:REWRITE DEFAULT-<-1))
 (347 330 (:REWRITE DEFAULT-<-2))
 (333 21 (:REWRITE CONSP-OF-NTHCDR))
 (332 310 (:REWRITE DEFAULT-+-1))
 (322 21 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (272 40 (:REWRITE SUM-LIST-WHEN-NAT-LISTP-AND-Z-LISTP))
 (216 9 (:DEFINITION BINARY-APPEND))
 (186 186 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (175 7 (:REWRITE TRUE-LISTP-OF-NTHCDR))
 (167 20 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (152 76 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (135 27 (:REWRITE CONSP-OF-TAKE))
 (128 32 (:REWRITE <-0-+-NEGATIVE-1))
 (126 18 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (122 14 (:REWRITE CAR-OF-NTHCDR))
 (116 116 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (116 116 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (110 22 (:DEFINITION TRUE-LISTP))
 (108 108 (:TYPE-PRESCRIPTION Z-LISTP))
 (108 14 (:DEFINITION NTH))
 (100 100 (:REWRITE DEFAULT-CAR))
 (64 64 (:REWRITE NTHCDR-WHEN-ATOM))
 (63 9 (:REWRITE CAR-OF-TAKE))
 (57 57 (:TYPE-PRESCRIPTION ZP))
 (56 14 (:REWRITE Z-LISTP-OF-CDR-WHEN-Z-LISTP))
 (54 54 (:REWRITE Z-LISTP-WHEN-NOT-CONSP))
 (49 41 (:REWRITE EQUAL-CONSTANT-+))
 (47 47 (:TYPE-PRESCRIPTION PARTITION))
 (40 40 (:REWRITE SUM-LIST-WHEN-NOT-CONSP))
 (32 32 (:REWRITE OPEN-SMALL-NTHCDR))
 (24 24 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE NATP-RW))
 )
(LEN-OF-CAR-OF-PARTITION
 (59 9 (:DEFINITION LEN))
 (52 52 (:TYPE-PRESCRIPTION PARTITION))
 (37 4 (:REWRITE TAKE-OF-LEN-FREE))
 (35 7 (:REWRITE CONSP-OF-PARTITION-UNDER-IFF))
 (24 1 (:DEFINITION NTHCDR))
 (21 12 (:REWRITE DEFAULT-+-2))
 (14 4 (:REWRITE ZP-OPEN))
 (13 10 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE DEFAULT-CDR))
 (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
 (10 10 (:REWRITE DEFAULT-<-2))
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7 7 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (4 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (4 1 (:REWRITE <-0-+-NEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
 (3 1 (:REWRITE COMMUTATIVITY-OF-+))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
