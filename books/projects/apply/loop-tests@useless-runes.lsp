(F1
 (33 3 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (27 3 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (6 6 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (6 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 3 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (6 3 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (6 3 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (3 3 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (3 3 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
(SQUARE
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(APPLY$-WARRANT-SQUARE)
(APPLY$-WARRANT-SQUARE-DEFINITION)
(APPLY$-WARRANT-SQUARE-NECC)
(APPLY$-SQUARE
 (8 8 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 (8 2 (:REWRITE DEFAULT-*-2))
 (6 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(F2
 (224 4 (:DEFINITION ALWAYS$))
 (138 4 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (98 1 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (65 1 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (65 1 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (55 5 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (55 1 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (44 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (40 5 (:DEFINITION FROM-TO-BY))
 (38 2 (:DEFINITION TRUE-LIST-LISTP))
 (30 3 (:DEFINITION TRUE-LISTP))
 (27 3 (:DEFINITION RATIONAL-LISTP))
 (25 5 (:DEFINITION BINARY-APPEND))
 (22 22 (:REWRITE DEFAULT-CAR))
 (22 2 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (22 2 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (19 19 (:REWRITE DEFAULT-CDR))
 (16 8 (:REWRITE APPLY$-PRIMP-BADGE))
 (16 4 (:REWRITE O-P-O-INFP-CAR))
 (16 2 (:DEFINITION SYMBOL-LISTP))
 (15 15 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (15 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 5 (:REWRITE COMMUTATIVITY-OF-+))
 (14 1 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (8 8 (:TYPE-PRESCRIPTION O-P))
 (6 6 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (6 6 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (5 5 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (4 4 (:REWRITE O-P-DEF-O-FINP-1))
 (4 4 (:REWRITE APPLY$-CONSP-ARITY-1))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (3 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (2 2 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (2 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (1 1 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (1 1 (:REWRITE APPLY$-WARRANT-SQUARE-NECC))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-FROM-TO-BY))
 )
(SUM-SQUARES)
(G)
(SUM$-REVAPPEND
 (68 43 (:REWRITE DEFAULT-+-2))
 (68 43 (:REWRITE DEFAULT-+-1))
 (57 19 (:REWRITE APPLY$-PRIMITIVE))
 (38 38 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (38 19 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (32 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (31 22 (:REWRITE DEFAULT-CAR))
 (26 17 (:REWRITE DEFAULT-CDR))
 (26 13 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (19 19 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (19 19 (:REWRITE APPLY$-CONSP-ARITY-1))
 (16 16 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (16 16 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (13 13 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (13 13 (:TYPE-PRESCRIPTION REVAPPEND))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 )
(SUM-CUBES)
(SUM-CUBES-RECURSIVE
 (6 6 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(SUM-CUBES-RECURSIVE-REVAPPEND
 (150 30 (:REWRITE DEFAULT-*-2))
 (112 56 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (104 36 (:REWRITE DEFAULT-+-2))
 (102 36 (:REWRITE DEFAULT-+-1))
 (88 52 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 (78 30 (:REWRITE DEFAULT-*-1))
 (63 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 56 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (56 56 (:TYPE-PRESCRIPTION REVAPPEND))
 (30 30 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (26 20 (:REWRITE DEFAULT-CAR))
 (21 15 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 )
(F2-ALT
 (2 2 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 )
(SUM-SQUARES-2
 (448 8 (:DEFINITION ALWAYS$))
 (276 8 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (196 2 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (130 2 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (130 2 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (110 10 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (110 2 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (88 4 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (80 10 (:DEFINITION FROM-TO-BY))
 (76 4 (:DEFINITION TRUE-LIST-LISTP))
 (60 6 (:DEFINITION TRUE-LISTP))
 (54 6 (:DEFINITION RATIONAL-LISTP))
 (50 10 (:DEFINITION BINARY-APPEND))
 (49 49 (:REWRITE DEFAULT-CAR))
 (44 4 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (44 4 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (42 42 (:REWRITE DEFAULT-+-2))
 (42 42 (:REWRITE DEFAULT-+-1))
 (40 40 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE APPLY$-PRIMP-BADGE))
 (32 8 (:REWRITE O-P-O-INFP-CAR))
 (32 4 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (28 2 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (16 16 (:TYPE-PRESCRIPTION O-P))
 (12 12 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (12 12 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (10 10 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE O-P-DEF-O-FINP-1))
 (8 8 (:REWRITE APPLY$-CONSP-ARITY-1))
 (6 6 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE TAMEP-TRUE-CAR/CDR-NESTP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (2 2 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE APPLY$-WARRANT-SQUARE-NECC))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-FROM-TO-BY))
 (1 1 (:REWRITE PLAIN-UQI-ALWAYS$))
 )
(SUM-SQUARES-3
 (224 4 (:DEFINITION ALWAYS$))
 (138 4 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (132 6 (:REWRITE APPLY$-PRIMITIVE))
 (120 6 (:META APPLY$-PRIM-META-FN-CORRECT))
 (98 1 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (65 1 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (65 1 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (55 5 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (55 1 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (44 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (40 5 (:DEFINITION FROM-TO-BY))
 (38 2 (:DEFINITION TRUE-LIST-LISTP))
 (30 3 (:DEFINITION TRUE-LISTP))
 (27 27 (:REWRITE DEFAULT-CAR))
 (27 27 (:REWRITE DEFAULT-+-2))
 (27 27 (:REWRITE DEFAULT-+-1))
 (27 3 (:DEFINITION RATIONAL-LISTP))
 (25 5 (:DEFINITION BINARY-APPEND))
 (22 22 (:TYPE-PRESCRIPTION ALWAYS$))
 (22 2 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (22 2 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (21 21 (:REWRITE DEFAULT-CDR))
 (16 8 (:REWRITE APPLY$-PRIMP-BADGE))
 (16 4 (:REWRITE O-P-O-INFP-CAR))
 (16 2 (:DEFINITION SYMBOL-LISTP))
 (15 15 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (14 14 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (14 1 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 1 (:REWRITE PLAIN-UQI-INTEGER-LISTP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (8 8 (:TYPE-PRESCRIPTION O-P))
 (6 6 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 6 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (5 5 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (4 4 (:REWRITE O-P-DEF-O-FINP-1))
 (4 4 (:REWRITE APPLY$-CONSP-ARITY-1))
 (3 3 (:REWRITE TAMEP-TRUE-CAR/CDR-NESTP))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:REWRITE INTEGER-LISTP-IMPLIES-ALWAYS$-INTEGERP))
 (3 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (1 1 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (1 1 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (1 1 (:REWRITE PLAIN-UQI-ALWAYS$))
 (1 1 (:REWRITE INTEGER-LISTP-FROM-TO-BY))
 (1 1 (:REWRITE APPLY$-WARRANT-SQUARE-NECC))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-FROM-TO-BY))
 )
(SUM-SQUARES-3
 (448 8 (:DEFINITION ALWAYS$))
 (276 8 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (196 2 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (130 2 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (130 2 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (110 10 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (110 2 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (88 4 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (80 10 (:DEFINITION FROM-TO-BY))
 (76 4 (:DEFINITION TRUE-LIST-LISTP))
 (60 6 (:DEFINITION TRUE-LISTP))
 (54 6 (:DEFINITION RATIONAL-LISTP))
 (50 10 (:DEFINITION BINARY-APPEND))
 (49 49 (:REWRITE DEFAULT-CAR))
 (44 4 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (44 4 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (42 42 (:REWRITE DEFAULT-+-2))
 (42 42 (:REWRITE DEFAULT-+-1))
 (40 40 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE APPLY$-PRIMP-BADGE))
 (32 8 (:REWRITE O-P-O-INFP-CAR))
 (32 4 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (28 2 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (16 16 (:TYPE-PRESCRIPTION O-P))
 (12 12 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (12 12 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (10 10 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE O-P-DEF-O-FINP-1))
 (8 8 (:REWRITE APPLY$-CONSP-ARITY-1))
 (6 6 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE TAMEP-TRUE-CAR/CDR-NESTP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (2 2 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE APPLY$-WARRANT-SQUARE-NECC))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-FROM-TO-BY))
 (1 1 (:REWRITE PLAIN-UQI-ALWAYS$))
 )
(DOUBLE)
(APPLY$-WARRANT-DOUBLE)
(APPLY$-WARRANT-DOUBLE-DEFINITION)
(APPLY$-WARRANT-DOUBLE-NECC)
(APPLY$-DOUBLE
 (8 2 (:REWRITE DEFAULT-+-2))
 (6 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(SUM-DOUBLES)
(SUM-DOUBLES
 (896 1 (:DEFINITION MEMBER-EQUAL))
 (824 12 (:DEFINITION ALWAYS$))
 (600 4 (:DEFINITION APPLY$-BADGEP))
 (428 4 (:DEFINITION INTEGER-LISTP))
 (411 8 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (396 12 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (321 12 (:DEFINITION SUBSETP-EQUAL))
 (300 33 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (223 3 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (203 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (134 134 (:REWRITE DEFAULT-CDR))
 (126 6 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (124 3 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (108 6 (:DEFINITION TRUE-LIST-LISTP))
 (100 3 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (99 99 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (90 9 (:DEFINITION TRUE-LISTP))
 (87 87 (:REWRITE DEFAULT-CAR))
 (72 3 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (62 3 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (60 12 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (60 6 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (57 6 (:DEFINITION NATP))
 (48 24 (:REWRITE APPLY$-PRIMP-BADGE))
 (48 12 (:REWRITE O-P-O-INFP-CAR))
 (47 5 (:DEFINITION RATIONAL-LISTP))
 (42 6 (:DEFINITION SYMBOL-LISTP))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (33 33 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (27 27 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (26 4 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (24 24 (:TYPE-PRESCRIPTION O-P))
 (24 24 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (22 4 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (21 21 (:TYPE-PRESCRIPTION LEN))
 (21 3 (:DEFINITION LEN))
 (18 18 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (18 18 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (18 9 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (18 3 (:DEFINITION ALL-NILS))
 (18 2 (:DEFINITION ACL2-NUMBER-LISTP))
 (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
 (14 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (13 13 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (12 12 (:REWRITE O-P-DEF-O-FINP-1))
 (12 12 (:REWRITE APPLY$-CONSP-ARITY-1))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (11 11 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (10 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (6 6 (:LINEAR BOUNDS-POSITION-EQUAL))
 (6 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (5 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE TAMEP-TRUE-CAR/CDR-NESTP))
 (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (2 2 (:REWRITE PLAIN-UQI-ALWAYS$))
 (2 2 (:REWRITE APPLY$-WARRANT-DOUBLE-NECC))
 )
(G1
 (1 1 (:TYPE-PRESCRIPTION G1))
 )
(APPLY$-WARRANT-G1)
(APPLY$-WARRANT-G1-DEFINITION)
(APPLY$-WARRANT-G1-NECC)
(APPLY$-G1
 (6 6 (:TYPE-PRESCRIPTION G1))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(G2)
(APPLY$-WARRANT-G2)
(APPLY$-WARRANT-G2-DEFINITION)
(APPLY$-WARRANT-G2-NECC)
(APPLY$-G2
 (10 2 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (6 6 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (6 3 (:REWRITE APPLY$-PRIMP-BADGE))
 (6 3 (:REWRITE APPLY$-PRIMITIVE))
 (4 4 (:REWRITE APPLY$-G1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE APPLY$-USERFN-ARITY-1))
 (2 2 (:REWRITE APPLY$-CONSP-ARITY-1))
 )
(LOOP1
 (234 22 (:REWRITE APPLY$-PRIMITIVE))
 (190 22 (:META APPLY$-PRIM-META-FN-CORRECT))
 (112 7 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (112 7 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (49 7 (:DEFINITION RATIONAL-LISTP))
 (42 42 (:TYPE-PRESCRIPTION ALWAYS$))
 (42 7 (:DEFINITION TRUE-LISTP))
 (32 7 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (29 29 (:REWRITE DEFAULT-CAR))
 (28 28 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (28 7 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (28 7 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (28 7 (:REWRITE PLAIN-UQI-INTEGER-LISTP))
 (22 22 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (22 22 (:REWRITE CAR-CONS))
 (22 22 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (17 17 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (11 11 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (7 7 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (7 7 (:REWRITE PLAIN-UQI-ALWAYS$))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (2 2 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (2 2 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE APPLY$-WARRANT-G2-NECC))
 )
(APPLY$-WARRANT-LOOP1)
(APPLY$-WARRANT-LOOP1-DEFINITION)
(APPLY$-WARRANT-LOOP1-NECC)
(APPLY$-LOOP1
 (24500 52 (:DEFINITION TAMEP))
 (24364 84 (:DEFINITION SUITABLY-TAMEP-LISTP))
 (23112 80 (:DEFINITION APPLY$-BADGEP))
 (18224 160 (:DEFINITION SUBSETP-EQUAL))
 (15024 1200 (:DEFINITION MEMBER-EQUAL))
 (14216 144 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (12348 16 (:REWRITE EV$-OPENER))
 (12192 8 (:REWRITE EV$-CONS))
 (10008 400 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (9440 640 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (9264 160 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (7206 7206 (:REWRITE DEFAULT-CDR))
 (4712 32 (:REWRITE ZP-OPEN))
 (2400 2400 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2080 2080 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (1920 1920 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (1852 1852 (:REWRITE DEFAULT-CAR))
 (1280 1280 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (1264 128 (:DEFINITION NATP))
 (1120 1120 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (656 656 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (400 400 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (320 160 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (320 40 (:DEFINITION TRUE-LISTP))
 (288 80 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (280 280 (:TYPE-PRESCRIPTION LEN))
 (280 40 (:DEFINITION LEN))
 (240 40 (:DEFINITION ALL-NILS))
 (208 96 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (208 80 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (200 200 (:TYPE-PRESCRIPTION ALL-NILS))
 (168 168 (:TYPE-PRESCRIPTION SUITABLY-TAMEP-LISTP))
 (160 160 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (160 160 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (160 160 (:REWRITE DEFAULT-<-2))
 (160 160 (:REWRITE DEFAULT-<-1))
 (140 140 (:TYPE-PRESCRIPTION TAMEP))
 (112 72 (:REWRITE DEFAULT-+-2))
 (96 96 (:REWRITE TAMEP-TRUE-CAR/CDR-NESTP))
 (80 80 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (74 37 (:REWRITE APPLY$-PRIMP-BADGE))
 (72 72 (:REWRITE DEFAULT-+-1))
 (56 56 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (56 56 (:LINEAR BOUNDS-POSITION-EQUAL))
 (46 46 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (40 40 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (20 11 (:REWRITE APPLY$-PRIMITIVE))
 (20 4 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (8 8 (:REWRITE APPLY$-G2))
 (8 8 (:REWRITE APPLY$-G1))
 (8 8 (:META RELINK-FANCY-SCION-CORRECT))
 (4 4 (:REWRITE APPLY$-CONSP-ARITY-1))
 )
