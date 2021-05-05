(PLIST-WORLDP-WITH-FORMALS-FORWARD-TO-PLIST-WORLDP
 (178 178 (:REWRITE DEFAULT-CAR))
 (104 104 (:REWRITE DEFAULT-CDR))
 (10 5 (:DEFINITION TRUE-LISTP))
 )
(PSEUDO-TERMP/PSEUDO-TERM-LISTP
 (250 105 (:REWRITE DEFAULT-+-2))
 (146 105 (:REWRITE DEFAULT-+-1))
 (95 95 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (40 10 (:DEFINITION INTEGER-ABS))
 (27 14 (:REWRITE DEFAULT-<-2))
 (18 14 (:REWRITE DEFAULT-<-1))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(TERM-LISTP-IMPLIES-TRUE-LISTP)
(ARGLISTP1-IMPLIES-SYMBOL-LISTP
 (11 11 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(STEP-1-LEMMA
 (390 390 (:REWRITE DEFAULT-CDR))
 (334 334 (:REWRITE DEFAULT-CAR))
 (168 84 (:REWRITE DEFAULT-+-2))
 (84 84 (:REWRITE DEFAULT-+-1))
 (43 43 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (42 42 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 )
(STEP-2-LEMMA
 (122 1 (:DEFINITION TERMP))
 (45 4 (:DEFINITION LENGTH))
 (35 7 (:DEFINITION LEN))
 (30 30 (:REWRITE DEFAULT-CDR))
 (25 25 (:REWRITE DEFAULT-CAR))
 (15 15 (:TYPE-PRESCRIPTION LEN))
 (14 7 (:REWRITE DEFAULT-+-2))
 (10 1 (:DEFINITION ARGLISTP))
 (9 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (8 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (7 7 (:REWRITE DEFAULT-+-1))
 (7 3 (:DEFINITION MEMBER-EQUAL))
 (6 1 (:DEFINITION ALL-VARS))
 (5 1 (:DEFINITION ALL-VARS1))
 (4 1 (:DEFINITION TERM-LISTP))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ARGLISTP1))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ADD-TO-SET-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION ARITY))
 (1 1 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 )
(ALL-VARS1/ALL-VARS1-LST)
(STEP-1-LEMMA
 (41 41 (:REWRITE DEFAULT-CAR))
 (38 38 (:REWRITE DEFAULT-CDR))
 (36 12 (:DEFINITION MEMBER-EQUAL))
 )
(STEP-2-LEMMA
 (283 283 (:REWRITE DEFAULT-CDR))
 (275 33 (:DEFINITION LENGTH))
 (254 254 (:REWRITE DEFAULT-CAR))
 (220 44 (:DEFINITION LEN))
 (99 99 (:TYPE-PRESCRIPTION LEN))
 (88 44 (:REWRITE DEFAULT-+-2))
 (44 44 (:REWRITE DEFAULT-+-1))
 (38 38 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (36 36 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (33 11 (:DEFINITION MEMBER-EQUAL))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-LISTP-ALL-VARS1
 (20 20 (:REWRITE DEFAULT-CDR))
 (20 4 (:DEFINITION LEN))
 (17 17 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 1 (:DEFINITION ALL-VARS1))
 (5 1 (:DEFINITION ADD-TO-SET-EQUAL))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-LISTP-IMPLIES-TRUE-LISTP)
(ARGLISTP1-IMPLIES-TRUE-LISTP
 (36 4 (:REWRITE SYMBOL-LISTP-IMPLIES-TRUE-LISTP))
 (24 4 (:DEFINITION SYMBOL-LISTP))
 (22 2 (:DEFINITION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 )
