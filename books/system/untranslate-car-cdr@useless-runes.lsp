(MAKE-REVERSED-AD-LIST
 (396 196 (:REWRITE DEFAULT-+-2))
 (264 196 (:REWRITE DEFAULT-+-1))
 (250 8 (:REWRITE O<=-O-FINP-DEF))
 (220 44 (:DEFINITION INTEGER-ABS))
 (184 60 (:META CANCEL_PLUS-LESSP-CORRECT))
 (176 44 (:REWRITE COMMUTATIVITY-OF-+))
 (176 22 (:DEFINITION LENGTH))
 (110 22 (:DEFINITION LEN))
 (72 58 (:REWRITE DEFAULT-<-2))
 (70 58 (:REWRITE DEFAULT-<-1))
 (58 58 (:REWRITE DEFAULT-CDR))
 (44 44 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 6 (:REWRITE O-P-O-INFP-CAR))
 (36 6 (:REWRITE O-FIRST-EXPT-<))
 (26 8 (:REWRITE AC-<))
 (24 12 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (22 22 (:TYPE-PRESCRIPTION LEN))
 (22 22 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (22 22 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (22 22 (:REWRITE DEFAULT-REALPART))
 (22 22 (:REWRITE DEFAULT-NUMERATOR))
 (22 22 (:REWRITE DEFAULT-IMAGPART))
 (22 22 (:REWRITE DEFAULT-DENOMINATOR))
 (22 22 (:REWRITE DEFAULT-COERCE-2))
 (22 22 (:REWRITE DEFAULT-COERCE-1))
 (16 8 (:REWRITE O-INFP-O-FINP-O<=))
 (12 12 (:TYPE-PRESCRIPTION O-FINP))
 (12 6 (:REWRITE O-FIRST-COEFF-<))
 (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(CAR-CDR-ABBREV-NAME)
(PRETTY-PARSE-AD-LIST
 (526 262 (:REWRITE DEFAULT-+-2))
 (352 262 (:REWRITE DEFAULT-+-1))
 (280 56 (:DEFINITION INTEGER-ABS))
 (224 56 (:REWRITE COMMUTATIVITY-OF-+))
 (224 28 (:DEFINITION LENGTH))
 (142 114 (:REWRITE DEFAULT-<-1))
 (116 114 (:REWRITE DEFAULT-<-2))
 (96 96 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE FOLD-CONSTS-IN-+))
 (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 48 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (28 28 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (28 28 (:REWRITE DEFAULT-REALPART))
 (28 28 (:REWRITE DEFAULT-NUMERATOR))
 (28 28 (:REWRITE DEFAULT-IMAGPART))
 (28 28 (:REWRITE DEFAULT-DENOMINATOR))
 (28 28 (:REWRITE DEFAULT-COERCE-2))
 (28 28 (:REWRITE DEFAULT-COERCE-1))
 (16 4 (:REWRITE O-P-O-INFP-CAR))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE O-P-DEF-O-FINP-1))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(UNTRANSLATE-CAR-CDR-NEST)
(AD-LISTP)
(DR-LISTP)
(ADR-LISTP)
(COMPOSE-AD)
(APPLY-FOR-DEFEVALUATOR)
(EVAD)
(EVAL-LIST-KWOTE-LST)
(FIX-TRUE-LIST-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(EVAD-CONSTRAINT-0)
(EVAD-CONSTRAINT-1)
(EVAD-CONSTRAINT-2)
(EVAD-CONSTRAINT-3)
(EVAD-CONSTRAINT-4)
(EVAD-CONSTRAINT-5)
(EVAD-CONSTRAINT-6)
(EVAD-CONSTRAINT-7)
(EVAD-CONSTRAINT-8)
(EVAD-CONSTRAINT-9)
(EVAD-CONSTRAINT-10)
(EVAD-CONSTRAINT-11)
(EVAD-CONSTRAINT-12)
(EVAD-CONSTRAINT-13)
(EVAD-CONSTRAINT-14)
(EVAD-CONSTRAINT-15)
(ENUMERATE-DR-LISTPS
 (50 50 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (50 50 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (41 41 (:REWRITE DEFAULT-CAR))
 (37 37 (:REWRITE DEFAULT-CDR))
 (22 12 (:REWRITE DEFAULT-<-2))
 (20 11 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (11 11 (:REWRITE DEFAULT-+-1))
 )
(ENUMERATE-ADR-LISTPS
 (191 191 (:REWRITE DEFAULT-CAR))
 (167 167 (:REWRITE DEFAULT-CDR))
 (155 155 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (155 155 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (55 29 (:REWRITE DEFAULT-+-2))
 (41 22 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE DEFAULT-<-1))
 (22 22 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(REV)
(EVAD-LIST-CAR-CDR-ABBREV-NAME
 (243 243 (:REWRITE DEFAULT-CAR))
 (113 113 (:REWRITE DEFAULT-CDR))
 (32 32 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (32 32 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (30 15 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE EVAD-CONSTRAINT-3))
 (16 16 (:REWRITE EVAD-CONSTRAINT-2))
 (16 16 (:REWRITE EVAD-CONSTRAINT-1))
 (15 15 (:REWRITE DEFAULT-+-1))
 (8 5 (:REWRITE DEFAULT-<-2))
 (7 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(EQUAL-EVAD-COMPOSE-AD-HINT)
(EQUAL-EVAD-COMPOSE-AD
 (620 620 (:TYPE-PRESCRIPTION COMPOSE-AD))
 (234 154 (:REWRITE DEFAULT-CAR))
 (128 28 (:REWRITE EVAD-CONSTRAINT-3))
 (124 32 (:REWRITE EVAD-CONSTRAINT-15))
 (124 32 (:REWRITE EVAD-CONSTRAINT-14))
 (124 32 (:REWRITE EVAD-CONSTRAINT-13))
 (124 32 (:REWRITE EVAD-CONSTRAINT-12))
 (124 32 (:REWRITE EVAD-CONSTRAINT-11))
 (124 32 (:REWRITE EVAD-CONSTRAINT-10))
 (112 28 (:REWRITE EVAD-CONSTRAINT-2))
 (110 110 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (110 110 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (60 60 (:REWRITE DEFAULT-CDR))
 (48 28 (:REWRITE EVAD-CONSTRAINT-1))
 (40 8 (:REWRITE O-P-O-INFP-CAR))
 (16 8 (:REWRITE O-P-DEF-O-FINP-1))
 )
(COMPOSE-AC-APPEND
 (84 69 (:REWRITE DEFAULT-CDR))
 (84 63 (:REWRITE DEFAULT-CAR))
 (49 49 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (49 49 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (42 21 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (21 21 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(MAKE-REVERSED-AD-LIST-SPEC
 (985 985 (:TYPE-PRESCRIPTION COMPOSE-AD))
 (444 364 (:REWRITE DEFAULT-CAR))
 (264 264 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (264 264 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (186 186 (:REWRITE DEFAULT-CDR))
 (167 34 (:REWRITE EVAD-CONSTRAINT-15))
 (165 30 (:REWRITE EVAD-CONSTRAINT-3))
 (157 34 (:REWRITE EVAD-CONSTRAINT-14))
 (157 34 (:REWRITE EVAD-CONSTRAINT-13))
 (157 34 (:REWRITE EVAD-CONSTRAINT-12))
 (157 34 (:REWRITE EVAD-CONSTRAINT-11))
 (157 34 (:REWRITE EVAD-CONSTRAINT-10))
 (149 30 (:REWRITE EVAD-CONSTRAINT-2))
 (85 30 (:REWRITE EVAD-CONSTRAINT-1))
 (70 28 (:REWRITE O-P-O-INFP-CAR))
 (22 10 (:REWRITE O-P-DEF-O-FINP-1))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 )
(DR-LISTP-LEN-1-REV
 (134 101 (:REWRITE DEFAULT-CDR))
 (127 94 (:REWRITE DEFAULT-CAR))
 (105 21 (:DEFINITION BINARY-APPEND))
 (86 86 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (46 25 (:REWRITE DEFAULT-+-2))
 (30 15 (:REWRITE O-INFP->NEQ-0))
 (25 25 (:REWRITE DEFAULT-+-1))
 )
(CAR-CDR-ABBREV-NAME-ADR-LIST-NOT-QUOTE
 (48 48 (:REWRITE DEFAULT-CDR))
 (41 41 (:REWRITE DEFAULT-CAR))
 (34 34 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (34 34 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (18 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(CAR-CDR-ABBREV-NAME-DR-LIST-NOT-QUOTE
 (99 99 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (99 99 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (90 90 (:REWRITE DEFAULT-CAR))
 (89 89 (:REWRITE DEFAULT-CDR))
 (38 21 (:REWRITE DEFAULT-<-2))
 (36 20 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (21 21 (:META CANCEL_PLUS-LESSP-CORRECT))
 (20 20 (:REWRITE DEFAULT-+-1))
 )
(EVAD-PRETTY-PARSE-AD-LIST-HINT
 (526 262 (:REWRITE DEFAULT-+-2))
 (352 262 (:REWRITE DEFAULT-+-1))
 (280 56 (:DEFINITION INTEGER-ABS))
 (224 56 (:REWRITE COMMUTATIVITY-OF-+))
 (224 28 (:DEFINITION LENGTH))
 (142 114 (:REWRITE DEFAULT-<-1))
 (116 114 (:REWRITE DEFAULT-<-2))
 (96 96 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE FOLD-CONSTS-IN-+))
 (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 48 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (28 28 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (28 28 (:REWRITE DEFAULT-REALPART))
 (28 28 (:REWRITE DEFAULT-NUMERATOR))
 (28 28 (:REWRITE DEFAULT-IMAGPART))
 (28 28 (:REWRITE DEFAULT-DENOMINATOR))
 (28 28 (:REWRITE DEFAULT-COERCE-2))
 (28 28 (:REWRITE DEFAULT-COERCE-1))
 (16 4 (:REWRITE O-P-O-INFP-CAR))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE O-P-DEF-O-FINP-1))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(EVAD-PRETTY-PARSE-AD-LIST
 (808 808 (:TYPE-PRESCRIPTION PRETTY-PARSE-AD-LIST))
 (432 332 (:REWRITE DEFAULT-CAR))
 (321 321 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (321 321 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (256 60 (:REWRITE EVAD-CONSTRAINT-9))
 (256 60 (:REWRITE EVAD-CONSTRAINT-8))
 (256 60 (:REWRITE EVAD-CONSTRAINT-2))
 (256 60 (:REWRITE EVAD-CONSTRAINT-15))
 (256 60 (:REWRITE EVAD-CONSTRAINT-14))
 (256 60 (:REWRITE EVAD-CONSTRAINT-13))
 (256 60 (:REWRITE EVAD-CONSTRAINT-12))
 (256 60 (:REWRITE EVAD-CONSTRAINT-11))
 (256 60 (:REWRITE EVAD-CONSTRAINT-10))
 (236 60 (:REWRITE EVAD-CONSTRAINT-3))
 (206 206 (:REWRITE DEFAULT-CDR))
 (198 198 (:TYPE-PRESCRIPTION COMPOSE-AD))
 (129 79 (:REWRITE DEFAULT-+-2))
 (106 60 (:REWRITE EVAD-CONSTRAINT-1))
 (79 79 (:REWRITE DEFAULT-+-1))
 (74 8 (:REWRITE DR-LISTP-LEN-1-REV))
 (50 10 (:REWRITE O-P-O-INFP-CAR))
 (30 6 (:DEFINITION BINARY-APPEND))
 (26 4 (:DEFINITION COMPOSE-AD))
 (20 14 (:REWRITE DEFAULT-<-1))
 (20 10 (:REWRITE O-P-DEF-O-FINP-1))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (18 6 (:REWRITE EQUAL-CONSTANT-+))
 (16 16 (:TYPE-PRESCRIPTION REV))
 (14 14 (:REWRITE DEFAULT-<-2))
 )
(COMPOSE-D)
(COMPOSE-D-LEMMA1
 (169 148 (:REWRITE DEFAULT-CDR))
 (155 134 (:REWRITE DEFAULT-CAR))
 (93 93 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (93 93 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(COMPOSE-D-LEMMA2
 (299 299 (:TYPE-PRESCRIPTION COMPOSE-D))
 (271 271 (:TYPE-PRESCRIPTION COMPOSE-AD))
 (100 94 (:REWRITE DEFAULT-CDR))
 (94 80 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (93 87 (:REWRITE DEFAULT-CAR))
 (80 80 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (15 3 (:DEFINITION BINARY-APPEND))
 (12 12 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (12 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (2 1 (:DEFINITION FIX))
 )
(REV-DR-LIST-IS-NO-OP
 (38 38 (:TYPE-PRESCRIPTION COMPOSE-AD))
 (29 2 (:REWRITE DR-LISTP-LEN-1-REV))
 (23 1 (:DEFINITION REV))
 (21 2 (:DEFINITION DR-LISTP))
 (12 2 (:DEFINITION COMPOSE-D))
 (11 11 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (5 1 (:DEFINITION LEN))
 (5 1 (:DEFINITION BINARY-APPEND))
 (2 2 (:TYPE-PRESCRIPTION REV))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(PRETTY-PARSE-AD-LIST-SPEC
 (1345 1345 (:TYPE-PRESCRIPTION COMPOSE-AD))
 (796 566 (:REWRITE DEFAULT-CAR))
 (656 656 (:TYPE-PRESCRIPTION PRETTY-PARSE-AD-LIST))
 (455 455 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (455 455 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (366 65 (:REWRITE EVAD-CONSTRAINT-14))
 (363 64 (:REWRITE EVAD-CONSTRAINT-12))
 (363 50 (:REWRITE EVAD-CONSTRAINT-3))
 (360 63 (:REWRITE EVAD-CONSTRAINT-10))
 (353 353 (:REWRITE DEFAULT-CDR))
 (325 50 (:REWRITE EVAD-CONSTRAINT-2))
 (128 50 (:REWRITE EVAD-CONSTRAINT-1))
 (127 74 (:REWRITE DEFAULT-+-2))
 (115 23 (:REWRITE O-P-O-INFP-CAR))
 (74 74 (:REWRITE DEFAULT-+-1))
 (56 56 (:TYPE-PRESCRIPTION CAR-CDR-ABBREV-NAME))
 (50 10 (:DEFINITION BINARY-APPEND))
 (46 23 (:REWRITE O-P-DEF-O-FINP-1))
 (30 21 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE DEFAULT-<-2))
 (20 20 (:TYPE-PRESCRIPTION REV))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (12 4 (:REWRITE EQUAL-CONSTANT-+))
 )
(UNTRANSLATE-CAR-CDR-NEST-CORRECT
 (112 8 (:DEFINITION MAKE-REVERSED-AD-LIST))
 (44 44 (:REWRITE DEFAULT-CAR))
 (33 33 (:TYPE-PRESCRIPTION PRETTY-PARSE-AD-LIST))
 (29 29 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (29 29 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (23 23 (:REWRITE DEFAULT-CDR))
 (12 2 (:DEFINITION PRETTY-PARSE-AD-LIST))
 (9 6 (:REWRITE EVAD-CONSTRAINT-9))
 (9 6 (:REWRITE EVAD-CONSTRAINT-8))
 (9 6 (:REWRITE EVAD-CONSTRAINT-3))
 (9 6 (:REWRITE EVAD-CONSTRAINT-2))
 (9 6 (:REWRITE EVAD-CONSTRAINT-15))
 (9 6 (:REWRITE EVAD-CONSTRAINT-14))
 (9 6 (:REWRITE EVAD-CONSTRAINT-13))
 (9 6 (:REWRITE EVAD-CONSTRAINT-12))
 (9 6 (:REWRITE EVAD-CONSTRAINT-11))
 (9 6 (:REWRITE EVAD-CONSTRAINT-10))
 (9 6 (:REWRITE EVAD-CONSTRAINT-1))
 )
