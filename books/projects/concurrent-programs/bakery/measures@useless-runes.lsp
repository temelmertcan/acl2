(MSRP)
(MSR<)
(MSR=0)
(MSR1-
 (145 68 (:REWRITE DEFAULT-+-2))
 (93 68 (:REWRITE DEFAULT-+-1))
 (48 12 (:REWRITE COMMUTATIVITY-OF-+))
 (48 6 (:DEFINITION LENGTH))
 (30 30 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION LEN))
 (27 22 (:REWRITE DEFAULT-<-2))
 (26 22 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE DEFAULT-REALPART))
 (6 6 (:REWRITE DEFAULT-NUMERATOR))
 (6 6 (:REWRITE DEFAULT-IMAGPART))
 (6 6 (:REWRITE DEFAULT-DENOMINATOR))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 )
(PUMP-ORD)
(MSR->ORD)
(BINARY-INDUCT
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(CONSP-PUMP-ORD-REDUCTION
 (14 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(PUMP-ORD-TYPE-PRESCRIPTION
 (13 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(E0-ORD-<-PUMP-ORD-M<N
 (42 14 (:REWRITE DEFAULT-CAR))
 (38 38 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE DEFAULT-<-1))
 (36 12 (:REWRITE ZP-OPEN))
 (35 35 (:REWRITE DEFAULT-+-2))
 (35 35 (:REWRITE DEFAULT-+-1))
 (34 6 (:REWRITE DEFAULT-CDR))
 (24 8 (:REWRITE FOLD-CONSTS-IN-+))
 )
(E0-ORD-<-ASYMMETRY
 (70 70 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-CDR))
 )
(PUMP-ORD-IS-AN-E0-ORDINALP
 (177 6 (:DEFINITION E0-ORD-<))
 (144 9 (:REWRITE E0-ORD-<-ASYMMETRY))
 (59 38 (:REWRITE DEFAULT-CAR))
 (48 48 (:TYPE-PRESCRIPTION E0-ORD-<))
 (44 23 (:REWRITE DEFAULT-CDR))
 (35 35 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE DEFAULT-<-1))
 (27 9 (:REWRITE CONSP-PUMP-ORD-REDUCTION))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ZP-OPEN))
 )
(CAR-MSR->ORD-CONDITIONAL
 (104 13 (:REWRITE ZP-OPEN))
 (78 51 (:REWRITE DEFAULT-+-2))
 (51 51 (:REWRITE DEFAULT-+-1))
 (34 21 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-CDR))
 (22 21 (:REWRITE DEFAULT-CAR))
 (21 21 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(PUMP-ORD-MAPS-E0-ORD-<-TO-<1
 (967 23 (:REWRITE E0-ORD-<-ASYMMETRY))
 (276 98 (:REWRITE CONSP-PUMP-ORD-REDUCTION))
 (266 70 (:REWRITE DEFAULT-CAR))
 (230 34 (:REWRITE DEFAULT-CDR))
 (153 153 (:REWRITE DEFAULT-<-2))
 (153 153 (:REWRITE DEFAULT-<-1))
 (36 22 (:REWRITE E0-ORD-<-PUMP-ORD-M<N))
 (22 22 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE ZP-OPEN))
 )
(PUMP-ORD-MAPS-E0-ORD-<-TO-<2
 (463 9 (:REWRITE E0-ORD-<-ASYMMETRY))
 (86 30 (:REWRITE DEFAULT-CAR))
 (83 83 (:REWRITE DEFAULT-<-2))
 (83 83 (:REWRITE DEFAULT-<-1))
 (70 14 (:REWRITE DEFAULT-CDR))
 (54 54 (:REWRITE DEFAULT-+-2))
 (54 54 (:REWRITE DEFAULT-+-1))
 (38 14 (:REWRITE ZP-OPEN))
 (30 10 (:REWRITE FOLD-CONSTS-IN-+))
 )
(MSR<-IMPLIES-EQUAL-LENGTHS
 (31 31 (:REWRITE DEFAULT-CAR))
 (28 14 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 )
(MSR->ORD-RETURNS-E0-ORDINALS
 (1018 18 (:DEFINITION E0-ORD-<))
 (519 35 (:DEFINITION PUMP-ORD))
 (332 74 (:REWRITE CONSP-PUMP-ORD-REDUCTION))
 (295 137 (:REWRITE DEFAULT-CAR))
 (276 118 (:REWRITE DEFAULT-CDR))
 (208 121 (:REWRITE DEFAULT-+-2))
 (208 26 (:REWRITE ZP-OPEN))
 (203 150 (:REWRITE DEFAULT-<-2))
 (153 150 (:REWRITE DEFAULT-<-1))
 (121 121 (:REWRITE DEFAULT-+-1))
 (67 10 (:REWRITE COMMUTATIVITY-2-OF-+))
 (40 40 (:REWRITE MSR<-IMPLIES-EQUAL-LENGTHS))
 (18 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(MSR<-IS-WELL-FOUNDED-VIA-MSR->ORD
 (1731 22 (:REWRITE E0-ORD-<-ASYMMETRY))
 (1112 44 (:REWRITE CAR-MSR->ORD-CONDITIONAL))
 (512 64 (:REWRITE ZP-OPEN))
 (388 236 (:REWRITE DEFAULT-+-2))
 (259 235 (:REWRITE DEFAULT-CAR))
 (236 236 (:REWRITE DEFAULT-+-1))
 (208 196 (:REWRITE DEFAULT-CDR))
 (193 114 (:REWRITE DEFAULT-<-2))
 (179 15 (:REWRITE E0-ORD-<-PUMP-ORD-M<N))
 (129 114 (:REWRITE DEFAULT-<-1))
 (44 44 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (26 2 (:REWRITE PUMP-ORD-MAPS-E0-ORD-<-TO-<2))
 )
(MSR-1-DECREASES-NON0-MEASURES
 (204 169 (:REWRITE DEFAULT-CAR))
 (147 119 (:REWRITE DEFAULT-CDR))
 (70 46 (:REWRITE DEFAULT-+-2))
 (57 57 (:REWRITE DEFAULT-<-2))
 (57 57 (:REWRITE DEFAULT-<-1))
 (46 46 (:REWRITE DEFAULT-+-1))
 (38 8 (:DEFINITION NATP))
 )
(MSR<-IS-IRREFLEXIVE
 (25 25 (:REWRITE DEFAULT-CAR))
 (20 4 (:DEFINITION LEN))
 (12 12 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE MSR<-IMPLIES-EQUAL-LENGTHS))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(MSR<-IS-ASYMMETRIC
 (153 153 (:REWRITE DEFAULT-CAR))
 (76 76 (:REWRITE DEFAULT-CDR))
 (60 30 (:REWRITE DEFAULT-+-2))
 (42 42 (:REWRITE DEFAULT-<-2))
 (42 42 (:REWRITE DEFAULT-<-1))
 (30 30 (:REWRITE DEFAULT-+-1))
 )
(MSR<-IS-TRANSITIVE
 (1011 1011 (:REWRITE DEFAULT-CAR))
 (730 730 (:REWRITE DEFAULT-CDR))
 (456 228 (:REWRITE DEFAULT-+-2))
 (258 258 (:REWRITE DEFAULT-<-2))
 (258 258 (:REWRITE DEFAULT-<-1))
 (228 228 (:REWRITE DEFAULT-+-1))
 )
(MSR<-CONS-REDUCTION
 (245 8 (:REWRITE MSR<-IS-ASYMMETRIC))
 (54 54 (:REWRITE DEFAULT-CDR))
 (52 52 (:REWRITE DEFAULT-CAR))
 (32 16 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE MSR<-IS-TRANSITIVE))
 (23 23 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE MSR<-IMPLIES-EQUAL-LENGTHS))
 (16 16 (:REWRITE DEFAULT-+-1))
 )
(NAT-LISTP-IS-TRUE-LISTP)
(LEN-APPEND-REDUCTION
 (46 23 (:REWRITE DEFAULT-+-2))
 (29 23 (:REWRITE DEFAULT-+-1))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (18 15 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE MSR<-IMPLIES-EQUAL-LENGTHS))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(MSR<-APPEND-REDUCTION
 (5410 126 (:REWRITE MSR<-IS-ASYMMETRIC))
 (1191 999 (:REWRITE DEFAULT-CAR))
 (1106 962 (:REWRITE DEFAULT-CDR))
 (1024 512 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (752 376 (:REWRITE DEFAULT-+-2))
 (512 512 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (512 512 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (456 376 (:REWRITE DEFAULT-+-1))
 (400 8 (:REWRITE MSR<-CONS-REDUCTION))
 (397 389 (:REWRITE MSR<-IS-TRANSITIVE))
 (327 327 (:REWRITE DEFAULT-<-2))
 (327 327 (:REWRITE DEFAULT-<-1))
 )
