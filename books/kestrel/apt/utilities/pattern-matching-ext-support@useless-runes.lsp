(DROP-FORMALS
 (5 5 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-LISTP-REVAPPEND
 (26 20 (:REWRITE DEFAULT-CAR))
 (21 15 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-LISTP-MV-NTH-0-DROP-FORMALS
 (52 52 (:REWRITE DEFAULT-CAR))
 (41 41 (:REWRITE DEFAULT-CDR))
 (27 9 (:DEFINITION REVAPPEND))
 (21 3 (:REWRITE DEFAULT-COERCE-3))
 (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (9 9 (:TYPE-PRESCRIPTION REVAPPEND))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(TRUE-LISTP-REVAPPEND
 (21 15 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(TRUE-LISTP-MV-NTH-1-DROP-FORMALS
 (27 9 (:DEFINITION REVAPPEND))
 (25 25 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE DEFAULT-CDR))
 (21 3 (:REWRITE DEFAULT-COERCE-3))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(ALL-VARS1/ALL-VARS1-LST)
(STEP-1-LEMMA
 (41 41 (:REWRITE DEFAULT-CAR))
 (38 38 (:REWRITE DEFAULT-CDR))
 (36 12 (:DEFINITION MEMBER-EQUAL))
 )
(STEP-2-LEMMA
 (275 33 (:DEFINITION LENGTH))
 (256 256 (:REWRITE DEFAULT-CDR))
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
 (20 4 (:DEFINITION LEN))
 (18 18 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 1 (:DEFINITION ALL-VARS1))
 (5 1 (:DEFINITION ADD-TO-SET-EQUAL))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(LEN-REVAPPEND
 (50 24 (:REWRITE DEFAULT-+-2))
 (30 24 (:REWRITE DEFAULT-+-1))
 (21 15 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(DROP-FORMALS-PRESERVES-EQUAL-LEN
 (112 16 (:REWRITE DEFAULT-COERCE-3))
 (89 89 (:REWRITE DEFAULT-CDR))
 (84 28 (:DEFINITION REVAPPEND))
 (70 70 (:REWRITE DEFAULT-CAR))
 (64 32 (:REWRITE DEFAULT-+-2))
 (32 32 (:REWRITE DEFAULT-COERCE-2))
 (32 32 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 )
(EQUAL-LEN-0-REWRITE
 (9 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(DROP-FORMALS-PRESERVES-EQUAL-LEN-0
 (45 9 (:DEFINITION ALL-VARS1))
 (22 4 (:DEFINITION LEN))
 (18 9 (:DEFINITION ADD-TO-SET-EQUAL))
 (15 15 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (9 9 (:DEFINITION MEMBER-EQUAL))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(EXT-MAKE-LAMBDA-APPLICATION
 (120 2 (:DEFINITION PSEUDO-TERMP))
 (60 12 (:DEFINITION LEN))
 (50 6 (:DEFINITION LENGTH))
 (42 42 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-+-2))
 (20 4 (:DEFINITION ALL-VARS1))
 (12 12 (:REWRITE DEFAULT-+-1))
 (9 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (8 4 (:DEFINITION ADD-TO-SET-EQUAL))
 (7 5 (:DEFINITION MEMBER-EQUAL))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(EXT-NEW-FORMAL)
(EXT-MAYBE-RENAME-FORMAL)
(EXT-RENAME-FORMALS)
(EXT-RESTORE-FORMALS)
(EXT-RENAME-FOR-SUBSTITUTION)
(EXT-FDEPOSIT-TERM-REC)
(EXT-FDEPOSIT-TERM)
(EXT-PREPROCESS-PAT-GUARD-HELPER
 (1 1 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 )
(EXT-PREPROCESS-PAT
 (1653 780 (:REWRITE DEFAULT-+-2))
 (1058 780 (:REWRITE DEFAULT-+-1))
 (602 86 (:DEFINITION LEN))
 (568 142 (:DEFINITION INTEGER-ABS))
 (301 209 (:REWRITE DEFAULT-<-2))
 (269 209 (:REWRITE DEFAULT-<-1))
 (142 142 (:REWRITE DEFAULT-UNARY-MINUS))
 (120 4 (:DEFINITION TAKE))
 (106 106 (:REWRITE DEFAULT-COERCE-2))
 (104 101 (:REWRITE DEFAULT-COERCE-1))
 (71 71 (:REWRITE DEFAULT-REALPART))
 (71 71 (:REWRITE DEFAULT-NUMERATOR))
 (71 71 (:REWRITE DEFAULT-IMAGPART))
 (71 71 (:REWRITE DEFAULT-DENOMINATOR))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (32 4 (:REWRITE ZP-OPEN))
 (16 5 (:REWRITE DEFAULT-COERCE-3))
 (13 3 (:REWRITE COERCE-INVERSE-1))
 (12 4 (:DEFINITION NTHCDR))
 (8 1 (:DEFINITION CHARACTER-LISTP))
 (7 7 (:REWRITE DEFAULT-SYMBOL-NAME))
 (1 1 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT))
 )
(EXT-GENEQV-AT-SUBTERM)
(PAT-VAR-P
 (14 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(NON-PAT-VARS1)
(PAT-UNIFY-SUBST)
(EQUAL-MOD-PATVARS
 (248 216 (:REWRITE DEFAULT-CAR))
 (174 84 (:REWRITE DEFAULT-+-2))
 (156 150 (:REWRITE DEFAULT-CDR))
 (117 84 (:REWRITE DEFAULT-+-1))
 (90 9 (:DEFINITION LENGTH))
 (72 18 (:REWRITE COMMUTATIVITY-OF-+))
 (72 18 (:DEFINITION INTEGER-ABS))
 (63 9 (:DEFINITION LEN))
 (27 21 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE FOLD-CONSTS-IN-+))
 (24 21 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE DEFAULT-SYMBOL-NAME))
 (21 21 (:REWRITE DEFAULT-COERCE-2))
 (21 21 (:REWRITE DEFAULT-COERCE-1))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (9 9 (:REWRITE DEFAULT-REALPART))
 (9 9 (:REWRITE DEFAULT-NUMERATOR))
 (9 9 (:REWRITE DEFAULT-IMAGPART))
 (9 9 (:REWRITE DEFAULT-DENOMINATOR))
 )
(EXT-ONE-WAY-UNIFY1-SIMPLE
 (1796 800 (:REWRITE DEFAULT-+-2))
 (1128 800 (:REWRITE DEFAULT-+-1))
 (624 92 (:DEFINITION LEN))
 (560 140 (:DEFINITION INTEGER-ABS))
 (326 326 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (276 184 (:REWRITE DEFAULT-<-2))
 (202 184 (:REWRITE DEFAULT-<-1))
 (168 20 (:REWRITE ZP-OPEN))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (100 10 (:DEFINITION PAT-VAR-P))
 (92 92 (:REWRITE DEFAULT-COERCE-2))
 (92 92 (:REWRITE DEFAULT-COERCE-1))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 10 (:DEFINITION CHAR))
 (40 10 (:DEFINITION NTH))
 (30 10 (:DEFINITION MEMBER-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 10 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(PSEUDO-TERM-REVAPPEND
 (124 2 (:DEFINITION PSEUDO-TERMP))
 (54 6 (:DEFINITION LENGTH))
 (50 48 (:REWRITE DEFAULT-CDR))
 (50 48 (:REWRITE DEFAULT-CAR))
 (44 8 (:DEFINITION LEN))
 (36 36 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 22 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERM-LISTP-FIRST-N-AC
 (124 2 (:DEFINITION PSEUDO-TERMP))
 (55 55 (:REWRITE DEFAULT-CDR))
 (55 55 (:REWRITE DEFAULT-CAR))
 (54 6 (:DEFINITION LENGTH))
 (44 8 (:DEFINITION LEN))
 (39 39 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (24 24 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (21 13 (:REWRITE DEFAULT-+-2))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (17 5 (:DEFINITION REVAPPEND))
 (13 13 (:REWRITE DEFAULT-+-1))
 (10 7 (:REWRITE ZP-OPEN))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(PSEUDO-TERM-LISTP-TAKE
 (62 1 (:DEFINITION PSEUDO-TERMP))
 (31 30 (:REWRITE DEFAULT-CDR))
 (31 30 (:REWRITE DEFAULT-CAR))
 (27 3 (:DEFINITION LENGTH))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 4 (:DEFINITION LEN))
 (15 15 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 8 (:REWRITE DEFAULT-+-2))
 (10 7 (:REWRITE ZP-OPEN))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(FLAG-EXT-ONE-WAY-UNIFY1-SIMPLE
 (1197 544 (:REWRITE DEFAULT-+-2))
 (764 544 (:REWRITE DEFAULT-+-1))
 (417 61 (:DEFINITION LEN))
 (400 100 (:DEFINITION INTEGER-ABS))
 (197 197 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (185 129 (:REWRITE DEFAULT-<-2))
 (145 129 (:REWRITE DEFAULT-<-1))
 (100 100 (:REWRITE DEFAULT-UNARY-MINUS))
 (84 10 (:REWRITE ZP-OPEN))
 (62 62 (:REWRITE DEFAULT-COERCE-2))
 (62 62 (:REWRITE DEFAULT-COERCE-1))
 (60 6 (:DEFINITION PAT-VAR-P))
 (50 50 (:REWRITE DEFAULT-REALPART))
 (50 50 (:REWRITE DEFAULT-NUMERATOR))
 (50 50 (:REWRITE DEFAULT-IMAGPART))
 (50 50 (:REWRITE DEFAULT-DENOMINATOR))
 (42 6 (:DEFINITION CHAR))
 (24 6 (:DEFINITION NTH))
 (18 6 (:DEFINITION MEMBER-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-EXT-ONE-WAY-UNIFY1-SIMPLE-EQUIVALENCES)
(FLAG-LEMMA-FOR-ALISTP-EXT-ONE-WAY-UNIFY1-SIMPLE-GUARD-HELPER
 (763 687 (:REWRITE DEFAULT-CAR))
 (723 669 (:REWRITE DEFAULT-CDR))
 (720 38 (:DEFINITION TAKE))
 (432 432 (:TYPE-PRESCRIPTION LEN))
 (368 38 (:REWRITE ZP-OPEN))
 (324 54 (:DEFINITION LEN))
 (146 92 (:REWRITE DEFAULT-+-2))
 (108 108 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (92 92 (:REWRITE DEFAULT-+-1))
 (92 38 (:REWRITE DEFAULT-<-2))
 (66 22 (:DEFINITION MEMBER-EQUAL))
 (49 49 (:REWRITE DEFAULT-COERCE-2))
 (49 49 (:REWRITE DEFAULT-COERCE-1))
 (44 44 (:REWRITE DEFAULT-SYMBOL-NAME))
 (38 38 (:REWRITE DEFAULT-<-1))
 )
(ALISTP-EXT-ONE-WAY-UNIFY1-SIMPLE-GUARD-HELPER)
(ALISTP-EXT-ONE-WAY-UNIFY1-SIMPLE-LST)
(EXT-ONE-WAY-UNIFY1-SIMPLE
 (1801 1792 (:REWRITE DEFAULT-CDR))
 (1087 555 (:REWRITE DEFAULT-+-2))
 (555 555 (:REWRITE DEFAULT-+-1))
 (370 37 (:DEFINITION PAT-VAR-P))
 (298 298 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (261 15 (:DEFINITION TAKE))
 (259 37 (:DEFINITION CHAR))
 (227 227 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (175 175 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (148 37 (:DEFINITION NTH))
 (132 15 (:REWRITE ZP-OPEN))
 (111 37 (:DEFINITION MEMBER-EQUAL))
 (104 104 (:REWRITE DEFAULT-COERCE-2))
 (104 104 (:REWRITE DEFAULT-COERCE-1))
 (92 1 (:DEFINITION EXT-ONE-WAY-UNIFY1-SIMPLE))
 (39 39 (:REWRITE DEFAULT-SYMBOL-NAME))
 (37 37 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (34 16 (:REWRITE DEFAULT-<-2))
 (33 3 (:DEFINITION EXT-ONE-WAY-UNIFY1-SIMPLE-LST))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (18 16 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 )
(APPLY-SUBST-TO-ALIST
 (1890 9 (:DEFINITION SUBLIS-VAR1))
 (1178 19 (:DEFINITION PSEUDO-TERMP))
 (891 9 (:DEFINITION CONS-TERM))
 (837 9 (:DEFINITION CONS-TERM1-MV2))
 (828 9 (:DEFINITION CONS-TERM1))
 (769 758 (:REWRITE DEFAULT-CAR))
 (558 558 (:DEFINITION KWOTE))
 (513 57 (:DEFINITION LENGTH))
 (418 76 (:DEFINITION LEN))
 (171 171 (:TYPE-PRESCRIPTION LEN))
 (170 94 (:REWRITE DEFAULT-+-2))
 (162 162 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (114 38 (:DEFINITION SYMBOL-LISTP))
 (108 18 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (94 94 (:REWRITE DEFAULT-+-1))
 (90 90 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (90 18 (:DEFINITION QUOTE-LISTP))
 (72 72 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (57 19 (:DEFINITION MEMBER-EQUAL))
 (55 55 (:REWRITE DEFAULT-COERCE-2))
 (54 54 (:REWRITE DEFAULT-<-2))
 (54 54 (:REWRITE DEFAULT-<-1))
 (54 18 (:DEFINITION CHARACTER-LISTP))
 (45 9 (:DEFINITION ASSOC-EQUAL))
 (38 38 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (37 37 (:REWRITE DEFAULT-COERCE-1))
 (36 36 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (36 36 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (36 18 (:REWRITE DEFAULT-PKG-IMPORTS))
 (36 18 (:DEFINITION QUOTEP))
 (27 27 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (18 18 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (18 18 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:REWRITE DEFAULT-UNARY-/))
 (18 18 (:REWRITE DEFAULT-SYMBOL-NAME))
 (18 18 (:REWRITE DEFAULT-REALPART))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (18 18 (:REWRITE DEFAULT-IMAGPART))
 (18 18 (:REWRITE DEFAULT-DENOMINATOR))
 (18 18 (:REWRITE DEFAULT-COMPLEX-2))
 (18 18 (:REWRITE DEFAULT-COMPLEX-1))
 (18 18 (:REWRITE DEFAULT-COERCE-3))
 (18 18 (:REWRITE DEFAULT-CODE-CHAR))
 (18 18 (:REWRITE DEFAULT-CHAR-CODE))
 (18 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 )
(EXTEND-BINDINGS
 (1890 9 (:DEFINITION SUBLIS-VAR1))
 (891 9 (:DEFINITION CONS-TERM))
 (837 9 (:DEFINITION CONS-TERM1-MV2))
 (828 9 (:DEFINITION CONS-TERM1))
 (558 558 (:DEFINITION KWOTE))
 (481 479 (:REWRITE DEFAULT-CDR))
 (463 461 (:REWRITE DEFAULT-CAR))
 (434 7 (:DEFINITION PSEUDO-TERMP))
 (216 117 (:REWRITE DEFAULT-+-2))
 (189 21 (:DEFINITION LENGTH))
 (162 162 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (117 117 (:REWRITE DEFAULT-+-1))
 (108 18 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (90 18 (:DEFINITION QUOTE-LISTP))
 (80 16 (:DEFINITION SYMBOL-ALISTP))
 (74 74 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (64 16 (:DEFINITION STRIP-CDRS))
 (54 54 (:REWRITE DEFAULT-<-2))
 (54 54 (:REWRITE DEFAULT-<-1))
 (54 18 (:DEFINITION CHARACTER-LISTP))
 (47 47 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (45 9 (:DEFINITION ASSOC-EQUAL))
 (43 43 (:REWRITE DEFAULT-COERCE-2))
 (36 36 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (36 36 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (36 18 (:REWRITE DEFAULT-PKG-IMPORTS))
 (36 18 (:DEFINITION QUOTEP))
 (27 27 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (25 25 (:REWRITE DEFAULT-COERCE-1))
 (18 18 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (18 18 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:REWRITE DEFAULT-UNARY-/))
 (18 18 (:REWRITE DEFAULT-SYMBOL-NAME))
 (18 18 (:REWRITE DEFAULT-REALPART))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (18 18 (:REWRITE DEFAULT-IMAGPART))
 (18 18 (:REWRITE DEFAULT-DENOMINATOR))
 (18 18 (:REWRITE DEFAULT-COMPLEX-2))
 (18 18 (:REWRITE DEFAULT-COMPLEX-1))
 (18 18 (:REWRITE DEFAULT-COERCE-3))
 (18 18 (:REWRITE DEFAULT-CODE-CHAR))
 (18 18 (:REWRITE DEFAULT-CHAR-CODE))
 (18 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 (14 14 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 )
(EXT-ADDRESS-SUBTERM-GOVERNORS-LST2
 (3463 1602 (:REWRITE DEFAULT-+-2))
 (2187 1602 (:REWRITE DEFAULT-+-1))
 (1600 160 (:DEFINITION LENGTH))
 (1584 16 (:DEFINITION CONS-TERM))
 (1488 16 (:DEFINITION CONS-TERM1-MV2))
 (1472 16 (:DEFINITION CONS-TERM1))
 (1280 320 (:DEFINITION INTEGER-ABS))
 (1120 160 (:DEFINITION LEN))
 (992 992 (:DEFINITION KWOTE))
 (608 483 (:REWRITE DEFAULT-<-2))
 (526 483 (:REWRITE DEFAULT-<-1))
 (352 352 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (352 352 (:REWRITE DEFAULT-UNARY-MINUS))
 (288 288 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (232 232 (:REWRITE DEFAULT-COERCE-2))
 (217 1 (:DEFINITION EXTEND-BINDINGS))
 (200 200 (:REWRITE DEFAULT-COERCE-1))
 (192 192 (:REWRITE DEFAULT-REALPART))
 (192 192 (:REWRITE DEFAULT-NUMERATOR))
 (192 192 (:REWRITE DEFAULT-IMAGPART))
 (192 192 (:REWRITE DEFAULT-DENOMINATOR))
 (192 32 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (160 160 (:TYPE-PRESCRIPTION LEN))
 (160 32 (:DEFINITION QUOTE-LISTP))
 (96 32 (:DEFINITION CHARACTER-LISTP))
 (80 8 (:DEFINITION PAT-VAR-P))
 (64 64 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (64 64 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (64 32 (:REWRITE DEFAULT-PKG-IMPORTS))
 (64 32 (:DEFINITION QUOTEP))
 (56 8 (:DEFINITION CHAR))
 (48 48 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (40 40 (:REWRITE DEFAULT-SYMBOL-NAME))
 (32 32 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (32 32 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (32 32 (:REWRITE DEFAULT-UNARY-/))
 (32 32 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (32 32 (:REWRITE DEFAULT-COMPLEX-2))
 (32 32 (:REWRITE DEFAULT-COMPLEX-1))
 (32 32 (:REWRITE DEFAULT-COERCE-3))
 (32 32 (:REWRITE DEFAULT-CODE-CHAR))
 (32 32 (:REWRITE DEFAULT-CHAR-CODE))
 (32 32 (:REWRITE DEFAULT-*-2))
 (32 32 (:REWRITE DEFAULT-*-1))
 (32 8 (:DEFINITION NTH))
 (24 8 (:DEFINITION MEMBER-EQUAL))
 (15 7 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (9 7 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION EXTEND-BINDINGS))
 (1 1 (:DEFINITION ACONS))
 )
(FLAG-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2
 (3663 1698 (:REWRITE DEFAULT-+-2))
 (2321 1698 (:REWRITE DEFAULT-+-1))
 (1700 170 (:DEFINITION LENGTH))
 (1584 16 (:DEFINITION CONS-TERM))
 (1488 16 (:DEFINITION CONS-TERM1-MV2))
 (1472 16 (:DEFINITION CONS-TERM1))
 (1360 340 (:DEFINITION INTEGER-ABS))
 (1190 170 (:DEFINITION LEN))
 (992 992 (:DEFINITION KWOTE))
 (640 508 (:REWRITE DEFAULT-<-2))
 (556 508 (:REWRITE DEFAULT-<-1))
 (372 372 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (372 372 (:REWRITE DEFAULT-UNARY-MINUS))
 (288 288 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (242 242 (:REWRITE DEFAULT-COERCE-2))
 (217 1 (:DEFINITION EXTEND-BINDINGS))
 (210 210 (:REWRITE DEFAULT-COERCE-1))
 (202 202 (:REWRITE DEFAULT-REALPART))
 (202 202 (:REWRITE DEFAULT-NUMERATOR))
 (202 202 (:REWRITE DEFAULT-IMAGPART))
 (202 202 (:REWRITE DEFAULT-DENOMINATOR))
 (192 32 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (170 170 (:TYPE-PRESCRIPTION LEN))
 (160 32 (:DEFINITION QUOTE-LISTP))
 (96 32 (:DEFINITION CHARACTER-LISTP))
 (80 8 (:DEFINITION PAT-VAR-P))
 (64 64 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (64 64 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (64 32 (:REWRITE DEFAULT-PKG-IMPORTS))
 (64 32 (:DEFINITION QUOTEP))
 (56 8 (:DEFINITION CHAR))
 (48 48 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (40 40 (:REWRITE DEFAULT-SYMBOL-NAME))
 (32 32 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (32 32 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (32 32 (:REWRITE DEFAULT-UNARY-/))
 (32 32 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (32 32 (:REWRITE DEFAULT-COMPLEX-2))
 (32 32 (:REWRITE DEFAULT-COMPLEX-1))
 (32 32 (:REWRITE DEFAULT-COERCE-3))
 (32 32 (:REWRITE DEFAULT-CODE-CHAR))
 (32 32 (:REWRITE DEFAULT-CHAR-CODE))
 (32 32 (:REWRITE DEFAULT-*-2))
 (32 32 (:REWRITE DEFAULT-*-1))
 (32 8 (:DEFINITION NTH))
 (24 8 (:DEFINITION MEMBER-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:DEFINITION ACONS))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2-EQUIVALENCES)
(FLAG-LEMMA-FOR-SYMBOL-ALISTP-EXT-ONE-WAY-UNIFY1-SIMPLE-GUARD-HELPER
 (1909 1800 (:REWRITE DEFAULT-CAR))
 (1698 1620 (:REWRITE DEFAULT-CDR))
 (1164 64 (:DEFINITION TAKE))
 (664 364 (:REWRITE DEFAULT-+-2))
 (592 64 (:REWRITE ZP-OPEN))
 (364 364 (:REWRITE DEFAULT-+-1))
 (164 164 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (148 64 (:REWRITE DEFAULT-<-2))
 (123 41 (:DEFINITION SYMBOL-LISTP))
 (108 108 (:REWRITE DEFAULT-COERCE-2))
 (108 108 (:REWRITE DEFAULT-COERCE-1))
 (104 104 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (93 93 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (93 31 (:DEFINITION MEMBER-EQUAL))
 (64 64 (:REWRITE DEFAULT-<-1))
 (57 57 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(SYMBOL-ALISTP-EXT-ONE-WAY-UNIFY1-SIMPLE-GUARD-HELPER)
(SYMBOL-ALISTP-EXT-ONE-WAY-UNIFY1-SIMPLE-LST)
(FLAG-LEMMA-FOR-TRUE-LISTP-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2
 (4434 739 (:DEFINITION EXTEND-BINDINGS))
 (2193 731 (:DEFINITION MEMBER-EQUAL))
 (739 739 (:DEFINITION ACONS))
 (731 731 (:REWRITE DEFAULT-SYMBOL-NAME))
 (731 731 (:REWRITE DEFAULT-COERCE-2))
 (731 731 (:REWRITE DEFAULT-COERCE-1))
 (27 14 (:REWRITE DEFAULT-+-2))
 (24 6 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(TRUE-LISTP-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2)
(EXT-ONE-WAY-UNIFY1-SIMPLE-LST-GUARD-HELPER)
(SYMBOL-ALISTP-APPEND
 (54 48 (:REWRITE DEFAULT-CAR))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (18 15 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(FLAG-LEMMA-FOR-SYMBOL-ALISTP-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2
 (17417 5809 (:DEFINITION BINARY-APPEND))
 (8946 1491 (:DEFINITION EXTEND-BINDINGS))
 (5805 2903 (:REWRITE DEFAULT-+-2))
 (4431 1477 (:DEFINITION MEMBER-EQUAL))
 (3238 3238 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3125 3125 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2903 2903 (:REWRITE DEFAULT-+-1))
 (2517 715 (:DEFINITION SYMBOL-LISTP))
 (2187 2187 (:REWRITE DEFAULT-COERCE-2))
 (2187 2187 (:REWRITE DEFAULT-COERCE-1))
 (1491 1491 (:DEFINITION ACONS))
 (1477 1477 (:REWRITE DEFAULT-SYMBOL-NAME))
 (32 8 (:REWRITE FOLD-CONSTS-IN-+))
 (17 17 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SYMBOL-ALISTP-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2)
(ALISTP-EXT-ADDRESS-SUBTERM-GOVERNORS-LST2-LST)
(PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERMP-CAR
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(PSEUDO-TERMP-SUBLIS-VAR
 (210 1 (:DEFINITION SUBLIS-VAR1))
 (99 1 (:DEFINITION CONS-TERM))
 (93 1 (:DEFINITION CONS-TERM1-MV2))
 (92 1 (:DEFINITION CONS-TERM1))
 (67 1 (:DEFINITION PSEUDO-TERMP))
 (62 62 (:DEFINITION KWOTE))
 (43 43 (:REWRITE DEFAULT-CAR))
 (41 41 (:REWRITE DEFAULT-CDR))
 (27 3 (:DEFINITION LENGTH))
 (22 4 (:DEFINITION LEN))
 (18 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (12 2 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (10 6 (:REWRITE DEFAULT-+-2))
 (10 2 (:REWRITE PSEUDO-TERM-LISTP-IMPLIES-PSEUDO-TERMP-CAR))
 (10 2 (:DEFINITION QUOTE-LISTP))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 2 (:DEFINITION CHARACTER-LISTP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 1 (:DEFINITION SYMBOL-ALISTP))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (4 4 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (4 2 (:REWRITE DEFAULT-PKG-IMPORTS))
 (4 2 (:DEFINITION QUOTEP))
 (4 1 (:DEFINITION STRIP-CDRS))
 (3 3 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (3 3 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (2 2 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COMPLEX-2))
 (2 2 (:REWRITE DEFAULT-COMPLEX-1))
 (2 2 (:REWRITE DEFAULT-COERCE-3))
 (2 2 (:REWRITE DEFAULT-CODE-CHAR))
 (2 2 (:REWRITE DEFAULT-CHAR-CODE))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(PSEUDO-TERM-LISTP-STRIP-CDRS-EXTEND-BINDINGS
 (840 4 (:DEFINITION SUBLIS-VAR1))
 (396 4 (:DEFINITION CONS-TERM))
 (372 4 (:DEFINITION CONS-TERM1-MV2))
 (368 4 (:DEFINITION CONS-TERM1))
 (248 248 (:DEFINITION KWOTE))
 (146 144 (:REWRITE DEFAULT-CAR))
 (138 136 (:REWRITE DEFAULT-CDR))
 (72 72 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (48 8 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (43 43 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (40 8 (:DEFINITION QUOTE-LISTP))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (24 8 (:DEFINITION CHARACTER-LISTP))
 (20 4 (:DEFINITION SYMBOL-ALISTP))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (16 16 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 8 (:REWRITE DEFAULT-PKG-IMPORTS))
 (16 8 (:DEFINITION QUOTEP))
 (13 13 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 12 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (8 8 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (8 8 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE DEFAULT-SYMBOL-NAME))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:REWRITE DEFAULT-COMPLEX-2))
 (8 8 (:REWRITE DEFAULT-COMPLEX-1))
 (8 8 (:REWRITE DEFAULT-COERCE-3))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:REWRITE DEFAULT-CODE-CHAR))
 (8 8 (:REWRITE DEFAULT-CHAR-CODE))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 )
(SYMBOL-ALISTP-EXTEND-BINDINGS
 (39 37 (:REWRITE DEFAULT-CAR))
 (16 15 (:REWRITE DEFAULT-CDR))
 )
(EXT-ADDRESS-SUBTERM-GOVERNORS-LST2
 (15826 15826 (:REWRITE DEFAULT-CDR))
 (15743 15604 (:REWRITE DEFAULT-CAR))
 (2381 1197 (:REWRITE DEFAULT-+-2))
 (2352 2352 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1390 139 (:DEFINITION PAT-VAR-P))
 (1252 1252 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1197 1197 (:REWRITE DEFAULT-+-1))
 (1046 1046 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (1026 342 (:DEFINITION BINARY-APPEND))
 (973 139 (:DEFINITION CHAR))
 (572 141 (:DEFINITION STRIP-CDRS))
 (556 139 (:DEFINITION NTH))
 (417 139 (:DEFINITION MEMBER-EQUAL))
 (384 384 (:REWRITE DEFAULT-COERCE-2))
 (384 384 (:REWRITE DEFAULT-COERCE-1))
 (139 139 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (139 139 (:REWRITE DEFAULT-SYMBOL-NAME))
 (138 138 (:REWRITE DEFAULT-<-2))
 (138 138 (:REWRITE DEFAULT-<-1))
 (132 132 (:DEFINITION ACONS))
 (27 3 (:DEFINITION EXT-ADDRESS-SUBTERM-GOVERNORS-LST2-LST))
 (14 14 (:TYPE-PRESCRIPTION EXTEND-BINDINGS))
 )
(EXT-ADDRESS-SUBTERM-GOVERNORS-LST1
 (2404 100 (:DEFINITION EQUAL-MOD-PATVARS))
 (1981 942 (:REWRITE DEFAULT-+-2))
 (1162 942 (:REWRITE DEFAULT-+-1))
 (972 324 (:DEFINITION BINARY-APPEND))
 (960 96 (:DEFINITION PAT-VAR-P))
 (672 96 (:DEFINITION CHAR))
 (658 658 (:TYPE-PRESCRIPTION EXT-PREPROCESS-PAT-GUARD-HELPER))
 (540 540 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (472 118 (:DEFINITION INTEGER-ABS))
 (384 96 (:DEFINITION NTH))
 (315 315 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (288 96 (:DEFINITION MEMBER-EQUAL))
 (233 233 (:REWRITE DEFAULT-COERCE-2))
 (233 233 (:REWRITE DEFAULT-COERCE-1))
 (228 182 (:REWRITE DEFAULT-<-2))
 (210 50 (:DEFINITION STRIP-CDRS))
 (198 182 (:REWRITE DEFAULT-<-1))
 (189 189 (:DEFINITION ACONS))
 (118 118 (:REWRITE DEFAULT-UNARY-MINUS))
 (96 96 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (96 96 (:TYPE-PRESCRIPTION EQUAL-MOD-PATVARS))
 (96 96 (:REWRITE DEFAULT-SYMBOL-NAME))
 (59 59 (:REWRITE DEFAULT-REALPART))
 (59 59 (:REWRITE DEFAULT-NUMERATOR))
 (59 59 (:REWRITE DEFAULT-IMAGPART))
 (59 59 (:REWRITE DEFAULT-DENOMINATOR))
 (20 20 (:TYPE-PRESCRIPTION EXTEND-BINDINGS))
 )
(EXT-ADDRESS-SUBTERM-GOVERNORS-LST-WORLD)
(EXT-ADDRESS-SUBTERM-GOVERNORS-LST)
(EXT-ADDRESS-SUBTERM-GOVERNORS-LST-STATE)
