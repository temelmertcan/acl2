(MODAPP::BADGE)
(MODAPP::BADGE-TYPE
 (111 1 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (45 45 (:REWRITE DEFAULT-CDR))
 (37 1 (:DEFINITION SUBSETP-EQUAL))
 (34 4 (:DEFINITION MEMBER-EQUAL))
 (24 4 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (12 12 (:REWRITE DEFAULT-CAR))
 (11 1 (:DEFINITION LEN))
 (9 1 (:DEFINITION NATP))
 (8 1 (:DEFINITION TRUE-LISTP))
 (6 1 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 1 (:DEFINITION ALL-NILS))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION ALL-NILS))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(MODAPP::TAMEP
 (602 276 (:REWRITE DEFAULT-+-2))
 (382 276 (:REWRITE DEFAULT-+-1))
 (256 14 (:REWRITE O<=-O-FINP-DEF))
 (184 46 (:DEFINITION INTEGER-ABS))
 (184 23 (:DEFINITION LENGTH))
 (144 144 (:REWRITE DEFAULT-CDR))
 (142 142 (:REWRITE DEFAULT-CAR))
 (115 23 (:DEFINITION LEN))
 (107 70 (:REWRITE DEFAULT-<-2))
 (104 26 (:REWRITE O-P-O-INFP-CAR))
 (94 70 (:REWRITE DEFAULT-<-1))
 (63 10 (:REWRITE O-FIRST-EXPT-<))
 (52 14 (:REWRITE AC-<))
 (48 8 (:DEFINITION SYMBOL-LISTP))
 (46 46 (:REWRITE DEFAULT-UNARY-MINUS))
 (43 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (28 14 (:REWRITE O-INFP-O-FINP-O<=))
 (26 26 (:REWRITE O-P-DEF-O-FINP-1))
 (24 6 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (23 23 (:TYPE-PRESCRIPTION LEN))
 (23 23 (:REWRITE DEFAULT-REALPART))
 (23 23 (:REWRITE DEFAULT-NUMERATOR))
 (23 23 (:REWRITE DEFAULT-IMAGPART))
 (23 23 (:REWRITE DEFAULT-DENOMINATOR))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (23 10 (:REWRITE O-FIRST-COEFF-<))
 (14 14 (:REWRITE |a < b & b < c  =>  a < c|))
 (12 6 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (6 6 (:TYPE-PRESCRIPTION MODAPP::APPLY$-BADGEP))
 (6 6 (:REWRITE ZP-OPEN))
 )
(MODAPP::TAMEP
 (3996 54 (:DEFINITION MODAPP::TAMEP))
 (2631 2631 (:REWRITE DEFAULT-CDR))
 (1260 315 (:REWRITE O-P-O-INFP-CAR))
 (1107 1107 (:REWRITE DEFAULT-CAR))
 (918 130 (:DEFINITION LEN))
 (882 126 (:DEFINITION SYMBOL-LISTP))
 (315 315 (:REWRITE O-P-DEF-O-FINP-1))
 (260 130 (:REWRITE DEFAULT-+-2))
 (142 4 (:DEFINITION SUBSETP-EQUAL))
 (130 130 (:REWRITE DEFAULT-+-1))
 (130 16 (:DEFINITION MEMBER-EQUAL))
 (78 13 (:DEFINITION TRUE-LISTP))
 (64 16 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (63 63 (:REWRITE DEFAULT-COERCE-2))
 (63 63 (:REWRITE DEFAULT-COERCE-1))
 (16 4 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (12 4 (:DEFINITION ALL-NILS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(MODAPP::SUITABLY-TAMEP-LISTP-INDUCTION)
(MODAPP::SUITABLY-TAMEP-LISTP-IMPLICANT-1
 (32 8 (:REWRITE O-P-O-INFP-CAR))
 (24 24 (:REWRITE DEFAULT-CAR))
 (12 11 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-+-1))
 (11 5 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE O-P-DEF-O-FINP-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE O-INFP->NEQ-0))
 )
(MODAPP::TAMEP-IMPLICANT-1
 (286 286 (:REWRITE DEFAULT-CDR))
 (135 19 (:DEFINITION LEN))
 (131 131 (:REWRITE DEFAULT-CAR))
 (128 32 (:REWRITE O-P-O-INFP-CAR))
 (116 5 (:DEFINITION MODAPP::SUITABLY-TAMEP-LISTP))
 (63 9 (:DEFINITION SYMBOL-LISTP))
 (44 5 (:REWRITE ZP-OPEN))
 (43 24 (:REWRITE DEFAULT-+-2))
 (37 1 (:DEFINITION SUBSETP-EQUAL))
 (34 4 (:DEFINITION MEMBER-EQUAL))
 (32 32 (:REWRITE O-P-DEF-O-FINP-1))
 (24 24 (:REWRITE DEFAULT-+-1))
 (22 9 (:DEFINITION TRUE-LISTP))
 (16 4 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (12 6 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-COERCE-2))
 (9 9 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 1 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (3 1 (:DEFINITION ALL-NILS))
 (1 1 (:TYPE-PRESCRIPTION MODAPP::TAMEP-FUNCTIONP))
 )
(MODAPP::EV$-MEASURE)
(MODAPP::EV$-LIST-MEASURE)
(MODAPP::APPLY$-MEASURE)
(MODAPP::APPLY$-LAMBDA-MEASURE)
(MODAPP::APPLY$
 (6400 62 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (6320 40 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (4213 2044 (:REWRITE DEFAULT-+-2))
 (3784 44 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (2721 2044 (:REWRITE DEFAULT-+-1))
 (2664 261 (:DEFINITION LENGTH))
 (2046 22 (:DEFINITION TRUE-LISTP))
 (1618 339 (:REWRITE O-P-O-INFP-CAR))
 (1576 394 (:DEFINITION INTEGER-ABS))
 (916 22 (:DEFINITION SUBSETP-EQUAL))
 (821 618 (:REWRITE DEFAULT-<-1))
 (784 88 (:DEFINITION MEMBER-EQUAL))
 (709 618 (:REWRITE DEFAULT-<-2))
 (601 339 (:REWRITE O-P-DEF-O-FINP-1))
 (594 66 (:DEFINITION SYMBOL-LISTP))
 (411 3 (:DEFINITION MODAPP::EV$))
 (394 394 (:REWRITE DEFAULT-UNARY-MINUS))
 (306 306 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (262 262 (:TYPE-PRESCRIPTION O-FINP))
 (261 261 (:REWRITE DEFAULT-COERCE-2))
 (261 261 (:REWRITE DEFAULT-COERCE-1))
 (197 197 (:REWRITE DEFAULT-REALPART))
 (197 197 (:REWRITE DEFAULT-NUMERATOR))
 (197 197 (:REWRITE DEFAULT-IMAGPART))
 (197 197 (:REWRITE DEFAULT-DENOMINATOR))
 (194 194 (:TYPE-PRESCRIPTION MODAPP::APPLY$-BADGEP))
 (176 88 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (157 23 (:DEFINITION NATP))
 (132 132 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (132 22 (:DEFINITION ALL-NILS))
 (110 110 (:TYPE-PRESCRIPTION ALL-NILS))
 (88 88 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (88 44 (:LINEAR MODAPP::APPLY$-BADGEP-PROPERTIES))
 (27 3 (:DEFINITION ASSOC-EQUAL))
 (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(MODAPP::APPLY$-LAMBDA-OPENER
 (278 2 (:DEFINITION MODAPP::EV$))
 (152 2 (:DEFINITION MODAPP::TAMEP))
 (133 109 (:REWRITE DEFAULT-CDR))
 (98 19 (:REWRITE O-P-O-INFP-CAR))
 (80 72 (:REWRITE DEFAULT-CAR))
 (41 19 (:REWRITE O-P-DEF-O-FINP-1))
 (38 38 (:TYPE-PRESCRIPTION O-P))
 (34 2 (:DEFINITION LENGTH))
 (33 3 (:DEFINITION PAIRLIS$))
 (28 4 (:DEFINITION LEN))
 (22 22 (:TYPE-PRESCRIPTION O-FINP))
 (22 2 (:DEFINITION ASSOC-EQUAL))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION PAIRLIS$))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(MODAPP::EV$-DEF-FACT
 (11274 2456 (:REWRITE O-P-O-INFP-CAR))
 (4630 27 (:DEFINITION MODAPP::APPLY$-USERFN))
 (4603 27 (:DEFINITION MODAPP::APPLY$-USERFN!))
 (4576 27 (:DEFINITION MODAPP::APPLY$-USERFN1!))
 (4018 574 (:DEFINITION LEN))
 (4002 2408 (:REWRITE O-P-DEF-O-FINP-1))
 (3381 483 (:DEFINITION SYMBOL-LISTP))
 (3335 135 (:DEFINITION MODAPP::TAMEP-FUNCTIONP!))
 (1941 221 (:DEFINITION ASSOC-EQUAL))
 (1528 1528 (:TYPE-PRESCRIPTION O-FINP))
 (1190 616 (:REWRITE DEFAULT-+-2))
 (616 616 (:REWRITE DEFAULT-+-1))
 (574 574 (:TYPE-PRESCRIPTION LEN))
 (459 27 (:REWRITE MODAPP::APPLY$-LAMBDA-OPENER))
 (442 442 (:TYPE-PRESCRIPTION MODAPP::EV$-LIST))
 (297 27 (:DEFINITION PAIRLIS$))
 (287 287 (:REWRITE DEFAULT-COERCE-2))
 (287 287 (:REWRITE DEFAULT-COERCE-1))
 (176 42 (:REWRITE ZP-OPEN))
 (155 21 (:DEFINITION MODAPP::NATS))
 (123 21 (:DEFINITION MODAPP::SQUARE))
 (105 105 (:TYPE-PRESCRIPTION MODAPP::TAMEP-FUNCTIONP!))
 (105 105 (:TYPE-PRESCRIPTION MODAPP::TAMEP!))
 (54 21 (:REWRITE DEFAULT-*-2))
 (48 42 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (48 21 (:REWRITE DEFAULT-*-1))
 (42 42 (:REWRITE DEFAULT-<-2))
 (42 42 (:REWRITE DEFAULT-<-1))
 (27 27 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (27 27 (:META MODAPP::APPLY$-PRIM-META-FN-CORRECT))
 )
(MODAPP::EV$-DEF)
(MODAPP::EV$-OPENER
 (3993 9 (:DEFINITION MODAPP::EV$))
 (2176 1948 (:REWRITE DEFAULT-CDR))
 (1622 2 (:DEFINITION MODAPP::APPLY$))
 (1428 287 (:REWRITE O-P-O-INFP-CAR))
 (1227 963 (:REWRITE DEFAULT-CAR))
 (884 52 (:DEFINITION LENGTH))
 (728 104 (:DEFINITION LEN))
 (668 2 (:DEFINITION MODAPP::APPLY$-USERFN))
 (666 2 (:DEFINITION MODAPP::APPLY$-USERFN!))
 (664 2 (:DEFINITION MODAPP::APPLY$-USERFN1!))
 (576 66 (:DEFINITION SYMBOL-LISTP))
 (567 287 (:REWRITE O-P-DEF-O-FINP-1))
 (470 470 (:TYPE-PRESCRIPTION MODAPP::EV$-LIST))
 (360 10 (:DEFINITION MODAPP::TAMEP-FUNCTIONP!))
 (270 270 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (212 108 (:REWRITE DEFAULT-+-2))
 (202 202 (:TYPE-PRESCRIPTION O-FINP))
 (164 3 (:DEFINITION MODAPP::SUITABLY-TAMEP-LISTP))
 (144 4 (:DEFINITION MODAPP::TAMEP-FUNCTIONP))
 (138 2 (:REWRITE MODAPP::APPLY$-LAMBDA-OPENER))
 (119 12 (:DEFINITION ASSOC-EQUAL))
 (108 108 (:REWRITE DEFAULT-+-1))
 (96 2 (:DEFINITION MODAPP::EV$-LIST))
 (52 52 (:REWRITE DEFAULT-COERCE-2))
 (52 52 (:REWRITE DEFAULT-COERCE-1))
 (34 2 (:DEFINITION PAIRLIS$))
 (28 2 (:DEFINITION MODAPP::SQUARE))
 (24 4 (:REWRITE ZP-OPEN))
 (22 2 (:DEFINITION MODAPP::NATS))
 (16 2 (:REWRITE DEFAULT-*-2))
 (10 10 (:TYPE-PRESCRIPTION MODAPP::TAMEP-FUNCTIONP!))
 (10 10 (:TYPE-PRESCRIPTION MODAPP::TAMEP!))
 (10 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 2 (:REWRITE DEFAULT-*-1))
 (4 4 (:TYPE-PRESCRIPTION MODAPP::TAMEP-FUNCTIONP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (2 2 (:META MODAPP::APPLY$-PRIM-META-FN-CORRECT))
 )
(MODAPP::EV$-LIST-DEF
 (276 2 (:DEFINITION MODAPP::EV$))
 (148 2 (:DEFINITION MODAPP::TAMEP))
 (123 99 (:REWRITE DEFAULT-CDR))
 (73 65 (:REWRITE DEFAULT-CAR))
 (72 16 (:REWRITE O-P-O-INFP-CAR))
 (34 2 (:DEFINITION LENGTH))
 (32 32 (:TYPE-PRESCRIPTION O-P))
 (28 4 (:DEFINITION LEN))
 (24 16 (:REWRITE O-P-DEF-O-FINP-1))
 (18 2 (:DEFINITION ASSOC-EQUAL))
 (15 15 (:REWRITE MODAPP::EV$-OPENER))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION O-FINP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(MODAPP::BETA-REDUCTION
 (15 3 (:DEFINITION PAIRLIS$))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE MODAPP::EV$-OPENER))
 )
(MODAPP::APPLY$-PRIMP-BADGE)
(MODAPP::BADGE-BADGE)
(MODAPP::BADGE-TAMEP)
(MODAPP::BADGE-TAMEP-FUNCTIONP)
(MODAPP::BADGE-SUITABLY-TAMEP-LISTP)
(MODAPP::BADGE-APPLY$)
(MODAPP::BADGE-EV$)
(MODAPP::APPLY$-PRIMITIVE
 (2 2 (:META MODAPP::APPLY$-PRIM-META-FN-CORRECT))
 )
(MODAPP::APPLY$-BADGE
 (6 2 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (5 5 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 )
(MODAPP::APPLY$-TAMEP
 (158 2 (:DEFINITION MODAPP::TAMEP))
 (58 58 (:REWRITE DEFAULT-CDR))
 (36 8 (:REWRITE O-P-O-INFP-CAR))
 (34 2 (:DEFINITION LENGTH))
 (28 4 (:DEFINITION LEN))
 (26 26 (:REWRITE DEFAULT-CAR))
 (16 16 (:TYPE-PRESCRIPTION O-P))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (12 8 (:REWRITE O-P-DEF-O-FINP-1))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (5 5 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 1 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 )
(MODAPP::APPLY$-TAMEP-FUNCTIONP
 (68 2 (:DEFINITION MODAPP::TAMEP-FUNCTIONP))
 (26 26 (:REWRITE DEFAULT-CDR))
 (20 4 (:REWRITE O-P-O-INFP-CAR))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (10 10 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION O-P))
 (8 4 (:REWRITE O-P-DEF-O-FINP-1))
 (6 2 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (5 5 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (2 2 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 1 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 )
(MODAPP::APPLY$-SUITABLY-TAMEP-LISTP
 (104 2 (:DEFINITION MODAPP::SUITABLY-TAMEP-LISTP))
 (52 10 (:REWRITE O-P-O-INFP-CAR))
 (38 26 (:REWRITE DEFAULT-CDR))
 (30 18 (:REWRITE DEFAULT-CAR))
 (22 10 (:REWRITE O-P-DEF-O-FINP-1))
 (20 20 (:TYPE-PRESCRIPTION O-P))
 (12 12 (:TYPE-PRESCRIPTION O-FINP))
 (8 2 (:REWRITE ZP-OPEN))
 (4 4 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (2 2 (:TYPE-PRESCRIPTION MODAPP::TAMEP-FUNCTIONP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:DEFINITION NOT))
 (2 1 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 (1 1 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 )
(MODAPP::APPLY$-APPLY$
 (590 124 (:REWRITE O-P-O-INFP-CAR))
 (578 2 (:DEFINITION MODAPP::APPLY$-USERFN))
 (576 2 (:DEFINITION MODAPP::APPLY$-USERFN!))
 (574 2 (:DEFINITION MODAPP::APPLY$-USERFN1!))
 (481 391 (:REWRITE DEFAULT-CDR))
 (418 202 (:REWRITE DEFAULT-CAR))
 (316 4 (:DEFINITION MODAPP::TAMEP))
 (310 10 (:DEFINITION MODAPP::TAMEP-FUNCTIONP!))
 (254 106 (:REWRITE O-P-DEF-O-FINP-1))
 (212 212 (:TYPE-PRESCRIPTION O-P))
 (148 148 (:TYPE-PRESCRIPTION O-FINP))
 (140 20 (:DEFINITION SYMBOL-LISTP))
 (104 2 (:DEFINITION MODAPP::SUITABLY-TAMEP-LISTP))
 (68 4 (:DEFINITION LENGTH))
 (56 8 (:DEFINITION LEN))
 (50 2 (:REWRITE MODAPP::APPLY$-LAMBDA-OPENER))
 (37 37 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (36 12 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (36 2 (:DEFINITION PAIRLIS$))
 (20 12 (:REWRITE DEFAULT-+-2))
 (17 6 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 (16 4 (:REWRITE ZP-OPEN))
 (14 2 (:DEFINITION MODAPP::NATS))
 (12 12 (:REWRITE DEFAULT-+-1))
 (10 10 (:TYPE-PRESCRIPTION MODAPP::TAMEP-FUNCTIONP!))
 (10 10 (:TYPE-PRESCRIPTION MODAPP::TAMEP!))
 (10 2 (:DEFINITION MODAPP::SQUARE))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE MODAPP::EV$-OPENER))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:META MODAPP::APPLY$-PRIM-META-FN-CORRECT))
 )
(MODAPP::APPLY$-EV$
 (61 61 (:REWRITE DEFAULT-CDR))
 (36 8 (:REWRITE O-P-O-INFP-CAR))
 (32 32 (:REWRITE DEFAULT-CAR))
 (28 4 (:DEFINITION LEN))
 (16 16 (:TYPE-PRESCRIPTION O-P))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (12 8 (:REWRITE O-P-DEF-O-FINP-1))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (5 5 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE MODAPP::EV$-OPENER))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 1 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 )
(MODAPP::EXECUTABLE-TAMEP)
(MODAPP::QUICK-CHECK-FOR-TAMENESSP)
(MODAPP::ACCUMULATE-ILK)
(MODAPP::CONVERT-ILK-ALIST-TO-ILKS1)
(MODAPP::CONVERT-ILK-ALIST-TO-ILKS)
(MODAPP::CHANGED-FUNCTIONAL-OR-EXPRESSIONAL-FORMALP)
(MODAPP::WELL-FORMED-LAMBDAP)
(MODAPP::GUESS-ILKS-ALIST)
(MODAPP::ANCESTRALLY-DEPENDENT-ON-APPLY$-USERFN-P1)
(MODAPP::ANCESTRALLY-DEPENDENT-ON-APPLY$-USERFN-P)
(MODAPP::ACCEPTABLE-WARRANTED-JUSTIFICATIONP)
(MODAPP::BADGER)
(MODAPP::COUNT-TO-NIL)
(MODAPP::EXECUTABLE-BADGE)
(MODAPP::EXECUTABLE-TAMEP
 (602 276 (:REWRITE DEFAULT-+-2))
 (382 276 (:REWRITE DEFAULT-+-1))
 (256 14 (:REWRITE O<=-O-FINP-DEF))
 (184 46 (:DEFINITION INTEGER-ABS))
 (184 23 (:DEFINITION LENGTH))
 (144 144 (:REWRITE DEFAULT-CDR))
 (142 142 (:REWRITE DEFAULT-CAR))
 (115 23 (:DEFINITION LEN))
 (107 70 (:REWRITE DEFAULT-<-2))
 (104 26 (:REWRITE O-P-O-INFP-CAR))
 (94 70 (:REWRITE DEFAULT-<-1))
 (63 10 (:REWRITE O-FIRST-EXPT-<))
 (52 14 (:REWRITE AC-<))
 (48 8 (:DEFINITION SYMBOL-LISTP))
 (46 46 (:REWRITE DEFAULT-UNARY-MINUS))
 (43 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (28 14 (:REWRITE O-INFP-O-FINP-O<=))
 (26 26 (:REWRITE O-P-DEF-O-FINP-1))
 (24 6 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (23 23 (:TYPE-PRESCRIPTION LEN))
 (23 23 (:REWRITE DEFAULT-REALPART))
 (23 23 (:REWRITE DEFAULT-NUMERATOR))
 (23 23 (:REWRITE DEFAULT-IMAGPART))
 (23 23 (:REWRITE DEFAULT-DENOMINATOR))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (23 10 (:REWRITE O-FIRST-COEFF-<))
 (14 14 (:REWRITE |a < b & b < c  =>  a < c|))
 (12 6 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (6 6 (:TYPE-PRESCRIPTION MODAPP::APPLY$-BADGEP))
 (6 6 (:REWRITE ZP-OPEN))
 )
(MODAPP::WELL-FORMED-LAMBDAP)
(MODAPP::CHANGED-FUNCTIONAL-OR-EXPRESSIONAL-FORMALP)
(MODAPP::ACCUMULATE-ILK)
(MODAPP::GUESS-ILKS-ALIST)
(MODAPP::FIND-BADGE-ILK)
(MODAPP::CHECK-ILKS)
(MODAPP::CHECKER
 (507 246 (:REWRITE DEFAULT-+-2))
 (342 246 (:REWRITE DEFAULT-+-1))
 (216 54 (:REWRITE COMMUTATIVITY-OF-+))
 (216 54 (:DEFINITION INTEGER-ABS))
 (216 27 (:DEFINITION LENGTH))
 (167 9 (:REWRITE O<=-O-FINP-DEF))
 (135 27 (:DEFINITION LEN))
 (82 64 (:REWRITE DEFAULT-<-2))
 (77 77 (:REWRITE DEFAULT-CDR))
 (74 64 (:REWRITE DEFAULT-<-1))
 (69 69 (:REWRITE FOLD-CONSTS-IN-+))
 (54 54 (:REWRITE DEFAULT-UNARY-MINUS))
 (53 53 (:REWRITE DEFAULT-CAR))
 (36 9 (:REWRITE O-P-O-INFP-CAR))
 (35 9 (:REWRITE AC-<))
 (27 27 (:TYPE-PRESCRIPTION LEN))
 (27 27 (:REWRITE DEFAULT-REALPART))
 (27 27 (:REWRITE DEFAULT-NUMERATOR))
 (27 27 (:REWRITE DEFAULT-IMAGPART))
 (27 27 (:REWRITE DEFAULT-DENOMINATOR))
 (27 27 (:REWRITE DEFAULT-COERCE-2))
 (27 27 (:REWRITE DEFAULT-COERCE-1))
 (18 9 (:REWRITE O-INFP-O-FINP-O<=))
 (9 9 (:REWRITE |a < b & b < c  =>  a < c|))
 (6 1 (:REWRITE O-FIRST-EXPT-<))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (2 1 (:REWRITE O-FIRST-COEFF-<))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(MODAPP::CHECKER-EQUIVALENCES)
(MODAPP::ALIST-OKP)
(MODAPP::FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-LEMMA
 (27234 306 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (26316 306 (:DEFINITION MODAPP::TAMEP))
 (15980 3648 (:REWRITE O-P-O-INFP-CAR))
 (13923 153 (:DEFINITION TRUE-LISTP))
 (7482 1158 (:DEFINITION LEN))
 (6111 679 (:DEFINITION ASSOC-EQUAL))
 (5036 3648 (:REWRITE O-P-DEF-O-FINP-1))
 (2316 1158 (:REWRITE DEFAULT-+-2))
 (2142 2142 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (1836 1836 (:TYPE-PRESCRIPTION MODAPP::SUITABLY-TAMEP-LISTP))
 (1388 1388 (:TYPE-PRESCRIPTION O-FINP))
 (1170 78 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (1158 1158 (:REWRITE DEFAULT-+-1))
 (1092 78 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (1014 78 (:DEFINITION ARGLISTP1))
 (918 306 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (858 78 (:DEFINITION ALL-VARS1))
 (612 612 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (540 540 (:REWRITE DEFAULT-COERCE-2))
 (540 540 (:REWRITE DEFAULT-COERCE-1))
 (295 59 (:DEFINITION MODAPP::FIND-BADGE-ILK))
 (156 156 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (156 78 (:DEFINITION ADD-TO-SET-EQUAL))
 (78 78 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 )
(MODAPP::GUESS-ILKS-ALIST-LEMMA)
(MODAPP::GUESS-ILKS-ALIST-LIST-LEMMA)
(MODAPP::BADGE-TABLE-OKP)
(MODAPP::APPLY$-BADGEP-HONS-GET-LEMMA
 (7948 96 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (7674 89 (:DEFINITION MODAPP::TAMEP))
 (7183 7153 (:REWRITE DEFAULT-CDR))
 (4613 48 (:DEFINITION TRUE-LISTP))
 (3958 228 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (3783 3783 (:REWRITE DEFAULT-CAR))
 (2080 520 (:REWRITE O-P-O-INFP-CAR))
 (1513 89 (:DEFINITION LENGTH))
 (1106 51 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (890 89 (:DEFINITION SYMBOL-LISTP))
 (623 623 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (534 534 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (534 534 (:TYPE-PRESCRIPTION MODAPP::SUITABLY-TAMEP-LISTP))
 (520 520 (:REWRITE O-P-DEF-O-FINP-1))
 (488 244 (:REWRITE DEFAULT-+-2))
 (267 89 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (244 244 (:REWRITE DEFAULT-+-1))
 (178 178 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (89 89 (:REWRITE DEFAULT-COERCE-2))
 (89 89 (:REWRITE DEFAULT-COERCE-1))
 (44 44 (:REWRITE DEFAULT-<-2))
 (44 44 (:REWRITE DEFAULT-<-1))
 )
(MODAPP::APPLY$-BADGEP-EXECUTABLE-BADGE-LEMMA
 (2850 34 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (2752 32 (:DEFINITION MODAPP::TAMEP))
 (2134 2134 (:REWRITE DEFAULT-CDR))
 (1619 17 (:DEFINITION TRUE-LISTP))
 (971 903 (:REWRITE DEFAULT-CAR))
 (864 78 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (650 15 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (544 32 (:DEFINITION LENGTH))
 (496 124 (:REWRITE O-P-O-INFP-CAR))
 (320 32 (:DEFINITION SYMBOL-LISTP))
 (224 224 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (192 192 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (192 192 (:TYPE-PRESCRIPTION MODAPP::SUITABLY-TAMEP-LISTP))
 (172 86 (:REWRITE DEFAULT-+-2))
 (124 124 (:REWRITE O-P-DEF-O-FINP-1))
 (96 32 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (86 86 (:REWRITE DEFAULT-+-1))
 (64 64 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (36 36 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (32 32 (:REWRITE DEFAULT-COERCE-2))
 (32 32 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 8 (:LINEAR MODAPP::APPLY$-BADGEP-PROPERTIES))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 )
(MODAPP::APPLY$-BADGEP-EXECUTABLE-BADGE
 (138 6 (:DEFINITION FGETPROP))
 (132 68 (:REWRITE DEFAULT-CAR))
 (120 30 (:REWRITE O-P-O-INFP-CAR))
 (104 56 (:REWRITE DEFAULT-CDR))
 (90 10 (:DEFINITION ASSOC-EQUAL))
 (60 60 (:TYPE-PRESCRIPTION O-P))
 (30 30 (:REWRITE O-P-DEF-O-FINP-1))
 (22 2 (:DEFINITION MODAPP::BADGE-TABLE-OKP))
 )
(MODAPP::FLAG-LEMMA-FOR-GUESS-ILKS-ALIST-CORRECT
 (408001 5177 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (392704 5060 (:DEFINITION MODAPP::TAMEP))
 (148070 35144 (:REWRITE O-P-O-INFP-CAR))
 (42638 35144 (:REWRITE O-P-DEF-O-FINP-1))
 (32636 32636 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (28968 28968 (:TYPE-PRESCRIPTION MODAPP::SUITABLY-TAMEP-LISTP))
 (26210 13105 (:REWRITE DEFAULT-+-2))
 (14484 5060 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (13105 13105 (:REWRITE DEFAULT-+-1))
 (9424 9424 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (7494 7494 (:TYPE-PRESCRIPTION O-FINP))
 (6945 463 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (6482 463 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (6019 463 (:DEFINITION ARGLISTP1))
 (5781 5781 (:REWRITE DEFAULT-COERCE-2))
 (5781 5781 (:REWRITE DEFAULT-COERCE-1))
 (5093 463 (:DEFINITION ALL-VARS1))
 (1023 1023 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (926 463 (:DEFINITION ADD-TO-SET-EQUAL))
 (651 610 (:REWRITE DEFAULT-<-1))
 (610 610 (:REWRITE DEFAULT-<-2))
 (510 510 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (31 31 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(MODAPP::GUESS-ILKS-ALIST-CORRECT)
(MODAPP::GUESS-ILKS-ALIST-LIST-CORRECT)
(MODAPP::APPLY$-EQUIVALENCE)
(MODAPP::APPLY$-EQUIVALENCE-NECC)
(MODAPP::FN-EQUAL)
(MODAPP::APPLY$-EQUIVALENCE-NECC-REWRITER
 (8 4 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 (4 4 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 )
(MODAPP::FN-EQUAL-IS-AN-EQUIVALENCE
 (208 208 (:REWRITE DEFAULT-CDR))
 (112 16 (:DEFINITION SYMBOL-LISTP))
 (64 64 (:REWRITE DEFAULT-CAR))
 (64 16 (:REWRITE O-P-O-INFP-CAR))
 (56 56 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (48 16 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (40 16 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 (32 32 (:TYPE-PRESCRIPTION O-P))
 (16 16 (:REWRITE O-P-DEF-O-FINP-1))
 (8 8 (:REWRITE MODAPP::APPLY$-EQUIVALENCE-NECC))
 )
(MODAPP::FN-EQUAL-IMPLIES-EQUAL-APPLY$-1
 (56 2 (:DEFINITION MODAPP::TAMEP-FUNCTIONP))
 (26 26 (:REWRITE DEFAULT-CDR))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE O-P-O-INFP-CAR))
 (6 6 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (6 2 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 (4 4 (:TYPE-PRESCRIPTION O-P))
 (4 2 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 (2 2 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE O-P-DEF-O-FINP-1))
 (2 2 (:REWRITE MODAPP::APPLY$-EQUIVALENCE-NECC-REWRITER))
 )
(MODAPP::DEFCONG-FN-EQUAL-EQUAL-EVENTS)
(MODAPP::WARRANT-NAME
 (30 30 (:REWRITE DEFAULT-SYMBOL-NAME))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (15 15 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE DEFAULT-CAR))
 )
(MODAPP::WARRANT-FN
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(MODAPP::TAMENESS-CONDITIONS)
(MODAPP::SUCCESSIVE-CADRS)
(MODAPP::NECC-NAME-ARGS-INSTANCE)
(MODAPP::DEF-WARRANT-EVENT)
(MODAPP::LAMB)
(MODAPP::CONSP-LAMB)
(MODAPP::CONSP-CDR-LAMB)
(MODAPP::CONSP-CDDR-LAMB)
(MODAPP::CDDDR-LAMB)
(MODAPP::CAR-LAMB)
(MODAPP::LAMBDA-FORMALS-LAMB)
(MODAPP::LAMBDA-BODY-LAMB)
(MODAPP::LAMB-REDUCTION)
(MODAPP::XLAMB)
