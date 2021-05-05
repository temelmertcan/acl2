(PROOF-CHECKER-ITP13::EVALUATE-LITERAL)
(PROOF-CHECKER-ITP13::EVALUATE-CLAUSE
 (50 12 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONJUNCTION))
 (39 3 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (20 20 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (20 20 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (20 20 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE DEFAULT-CAR))
 (18 6 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (6 6 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (6 6 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (3 3 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (3 2 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (3 2 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-NOT-SUBSETP-IMPLIES-NOT-NO-CONFLICTING-LITERALSP))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::NOT-NO-CONFLICTING-LITERALSP))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::FORMULAP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 )
(PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-CLAUSE
 (76 76 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (76 76 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (60 60 (:REWRITE DEFAULT-CAR))
 (46 46 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 )
(PROOF-CHECKER-ITP13::EVALUATE-FORMULA)
(PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA
 (684 12 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (252 12 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (156 24 (:DEFINITION MEMBER-EQUAL))
 (48 48 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (48 48 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (48 48 (:REWRITE DEFAULT-CAR))
 (41 41 (:REWRITE DEFAULT-CDR))
 (24 24 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (24 24 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (24 24 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 )
(PROOF-CHECKER-ITP13::IFF-TRUEP-EVALUATE-CLAUSE-CONS
 (227 227 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (227 227 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (198 198 (:REWRITE DEFAULT-CAR))
 (137 137 (:REWRITE DEFAULT-CDR))
 (88 88 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 )
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-FORMULA-CONS
 (631 112 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (627 11 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (274 105 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (231 11 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (143 22 (:DEFINITION MEMBER-EQUAL))
 (127 68 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (107 47 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-FALSEP))
 (103 62 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (77 49 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-UNDEFP))
 (77 47 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (63 63 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA))
 (44 44 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (44 44 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (39 39 (:REWRITE DEFAULT-CDR))
 (39 39 (:REWRITE DEFAULT-CAR))
 (22 22 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (22 22 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (22 22 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (5 5 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-FALSE))
 )
(PROOF-CHECKER-ITP13::NOT-UNDEFP-EVALUATE-CLAUSE-CONS
 (823 823 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (823 823 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (609 609 (:REWRITE DEFAULT-CAR))
 (473 473 (:REWRITE DEFAULT-CDR))
 (128 128 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 )
(PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL
 (23464 616 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (23436 210 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (21658 70 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP))
 (21616 616 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (21448 70 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (20720 70 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-CDR))
 (19222 28 (:DEFINITION PROOF-CHECKER-ITP13::SUBSETP))
 (12659 1810 (:DEFINITION MEMBER-EQUAL))
 (10360 70 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))
 (4886 4886 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (4064 4064 (:REWRITE DEFAULT-CDR))
 (4064 4064 (:REWRITE DEFAULT-CAR))
 (3626 3626 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (1748 1748 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (1746 1746 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (1372 1372 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (616 616 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (70 70 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (70 70 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 (7 7 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (3 3 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 )
(PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE
 (43576 1144 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (43524 390 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (40222 130 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP))
 (40144 1144 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (39832 130 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (38480 130 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-CDR))
 (35698 52 (:DEFINITION PROOF-CHECKER-ITP13::SUBSETP))
 (19240 130 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))
 (9074 9074 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (7720 7720 (:REWRITE DEFAULT-CAR))
 (7691 7691 (:REWRITE DEFAULT-CDR))
 (6936 6936 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (3329 3329 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (2548 2548 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (1144 1144 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (147 43 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONJUNCTION))
 (130 130 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (130 130 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 (36 36 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (18 6 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (15 15 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-NOT-SUBSETP-IMPLIES-NOT-NO-CONFLICTING-LITERALSP))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::NOT-NO-CONFLICTING-LITERALSP))
 (10 10 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 )
(PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA
 (2079 7 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SET-EQUALP))
 (2058 7 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (1512 42 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (1512 14 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (1386 42 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (1044 18 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (480 480 (:REWRITE DEFAULT-CDR))
 (474 474 (:REWRITE DEFAULT-CAR))
 (436 436 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (436 436 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (416 96 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONJUNCTION))
 (400 16 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (378 18 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (336 336 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (180 180 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (180 180 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (144 48 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (91 91 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (64 16 (:REWRITE PROOF-CHECKER-ITP13::FORMULAP-MEMBER))
 (42 42 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (18 18 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (17 17 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-NOT-SUBSETP-IMPLIES-NOT-NO-CONFLICTING-LITERALSP))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::NOT-NO-CONFLICTING-LITERALSP))
 (8 2 (:REWRITE PROOF-CHECKER-ITP13::FORMULAP-CDR))
 (7 7 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (7 7 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 )
(PROOF-CHECKER-ITP13::SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::LITERAL-LISTP-SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::UNIQUE-LITERALSP-SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::NO-CONFLICTING-LITERALSP-SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::ASSIGNMENTP-SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::SUBSETP-SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-SHORTEN-LONG-ASSIGNMENT)
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-LITERAL-SHORTEN-LONG-ASSIGNMENT
 (134 18 (:DEFINITION MEMBER-EQUAL))
 (84 3 (:DEFINITION PROOF-CHECKER-ITP13::UNION-VARIABLES))
 (43 5 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES3))
 (36 36 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (36 36 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (30 30 (:REWRITE DEFAULT-CAR))
 (27 27 (:REWRITE DEFAULT-CDR))
 (18 18 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (18 18 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (8 8 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::UNION-VARIABLES))
 (7 5 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (7 5 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (6 3 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (6 3 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (6 1 (:REWRITE PROOF-CHECKER-ITP13::NEGATE-NEGATE))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (3 1 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (3 1 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (2 2 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 )
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-SHORTEN-LONG-ASSIGNMENT
 (42882 357 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (42504 1071 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (39333 1155 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (35742 91 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP))
 (35469 91 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (27468 91 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-CDR))
 (22120 91 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))
 (9072 9072 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (8247 8247 (:REWRITE DEFAULT-CAR))
 (8171 8171 (:REWRITE DEFAULT-CDR))
 (3608 3608 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (2261 2261 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (2184 39 (:DEFINITION PROOF-CHECKER-ITP13::UNION-VARIABLES))
 (1430 64 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES3))
 (1071 1071 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (91 91 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (91 91 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 (66 11 (:REWRITE PROOF-CHECKER-ITP13::NEGATE-NEGATE))
 (57 57 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (48 8 (:REWRITE PROOF-CHECKER-ITP13::LITERALP-IMPLIES-NOT-EQUAL-NEGATE))
 (38 38 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (38 38 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (19 19 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (19 19 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (19 19 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 )
(PROOF-CHECKER-ITP13::SUBSETP-LIST-TRUEP-EVALUATE-FORMULA-SHORTEN-LONG-ASSIGNMENT
 (63180 1755 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (63180 585 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (57915 1755 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (57915 195 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP))
 (57330 195 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (53547 78 (:DEFINITION PROOF-CHECKER-ITP13::SUBSETP))
 (53352 195 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-CDR))
 (34263 4976 (:DEFINITION MEMBER-EQUAL))
 (28860 195 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))
 (14040 14040 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (11711 11711 (:REWRITE DEFAULT-CDR))
 (11690 11690 (:REWRITE DEFAULT-CAR))
 (9952 9952 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (9952 9952 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (7472 7472 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6377 109 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (4898 4898 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (4898 4898 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (3900 3900 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (2453 109 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (1755 1755 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (195 195 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (195 195 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 (164 164 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SHORTEN-LONG-ASSIGNMENT))
 (109 109 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (109 109 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (36 36 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-TRUE))
 )
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-FORMULA-SHORTEN-LONG-ASSIGNMENT
 (380 2 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-FORMULA))
 (227 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (211 37 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (196 34 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (126 35 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (121 8 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-SHORTEN-LONG-ASSIGNMENT))
 (88 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (56 8 (:DEFINITION MEMBER-EQUAL))
 (52 52 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-CLAUSE))
 (39 18 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (32 20 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (32 18 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (32 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-FALSEP))
 (26 14 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (24 24 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA))
 (23 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-UNDEFP))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (4 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SHORTEN-LONG-ASSIGNMENT))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 )
(PROOF-CHECKER-ITP13::STRONG-ASSIGNMENT-SHORTEN-LONG-ASSIGNMENT
 (380 2 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-FORMULA))
 (227 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (211 37 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (196 34 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (126 35 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (121 8 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-SHORTEN-LONG-ASSIGNMENT))
 (88 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (56 8 (:DEFINITION MEMBER-EQUAL))
 (52 52 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-CLAUSE))
 (39 18 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (32 20 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (32 18 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (32 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-FALSEP))
 (26 14 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (24 24 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA))
 (23 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-UNDEFP))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (9 2 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-LIST-TRUEP-EVALUATE-FORMULA-SHORTEN-LONG-ASSIGNMENT))
 (8 8 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (4 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SHORTEN-LONG-ASSIGNMENT))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 )
(PROOF-CHECKER-ITP13::EXTEND-SHORT-ASSIGNMENT)
(PROOF-CHECKER-ITP13::LITERAL-LISTP-EXTEND-SHORT-ASSIGNMENT
 (1163 35 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (1001 10 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-APPEND))
 (847 10 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-SET-DIFFERENCE-VARIABLES))
 (637 9 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-APPEND))
 (323 35 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (321 321 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (311 311 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (266 258 (:REWRITE DEFAULT-CAR))
 (262 254 (:REWRITE DEFAULT-CDR))
 (134 10 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS2))
 (130 10 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS3))
 (92 92 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (91 1 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONS))
 (66 22 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (35 35 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (19 19 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (13 1 (:REWRITE PROOF-CHECKER-ITP13::NOT-MEMBER-REMOVE-CONFLICTING-LITERALS))
 (7 1 (:REWRITE PROOF-CHECKER-ITP13::LITERALP-IMPLIES-NOT-EQUAL-NEGATE))
 )
(PROOF-CHECKER-ITP13::UNIQUE-LITERALSP-EXTEND-SHORT-ASSIGNMENT
 (182 170 (:REWRITE DEFAULT-CDR))
 (163 155 (:REWRITE DEFAULT-CAR))
 (123 123 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (122 122 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (56 56 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (42 14 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (20 20 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 1 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS3))
 (6 1 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONS))
 (4 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS2))
 )
(PROOF-CHECKER-ITP13::NO-CONFLICTING-LITERALSP-EXTEND-SHORT-ASSIGNMENT
 (155 143 (:REWRITE DEFAULT-CDR))
 (141 133 (:REWRITE DEFAULT-CAR))
 (101 101 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (100 100 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (70 70 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (24 8 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (20 20 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (18 18 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-NOT-SUBSETP-IMPLIES-NOT-NO-CONFLICTING-LITERALSP))
 (18 18 (:REWRITE PROOF-CHECKER-ITP13::NOT-NO-CONFLICTING-LITERALSP))
 (9 1 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS3))
 (6 1 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONS))
 (5 1 (:REWRITE PROOF-CHECKER-ITP13::LITERALP-NEGATE))
 (4 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (3 3 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (3 3 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS2))
 )
(PROOF-CHECKER-ITP13::ASSIGNMENTP-EXTEND-SHORT-ASSIGNMENT)
(PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-EXTEND-SHORT-ASSIGNMENT
 (5420 253 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS2))
 (4577 4577 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (4361 4361 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (4141 86 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (3117 3061 (:REWRITE DEFAULT-CAR))
 (2815 2782 (:REWRITE DEFAULT-CDR))
 (2143 2133 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (780 780 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (780 780 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (770 64 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-AND-NOT-MEMBER-IMPLIES-NOT-SUBSET-VARIABLESP))
 (174 34 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONJUNCTION))
 (129 5 (:REWRITE PROOF-CHECKER-ITP13::EQUAL-SET-DIFFERENCE-VARIABLES-CONS))
 (116 116 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::ASSIGNMENTP))
 (82 82 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (72 24 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 )
(PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-EXTEND-SHORT-ASSIGNMENT2
 (357 10 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (356 10 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (84 11 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (75 75 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (64 64 (:REWRITE DEFAULT-CAR))
 (61 61 (:REWRITE DEFAULT-CDR))
 (56 56 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (54 54 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (20 20 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (18 1 (:DEFINITION PROOF-CHECKER-ITP13::REMOVE-CONFLICTING-LITERALS))
 (9 9 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-AND-NOT-MEMBER-IMPLIES-NOT-SUBSET-VARIABLESP))
 (9 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (5 1 (:DEFINITION BINARY-APPEND))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (2 2 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::REMOVE-CONFLICTING-LITERALS))
 )
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-LITERAL-EXTEND-LONG-ASSIGNMENT
 (87 3 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (85 5 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS2))
 (83 83 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (78 78 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (60 60 (:REWRITE DEFAULT-CDR))
 (57 57 (:REWRITE DEFAULT-CAR))
 (54 3 (:DEFINITION PROOF-CHECKER-ITP13::REMOVE-CONFLICTING-LITERALS))
 (46 46 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (37 5 (:REWRITE PROOF-CHECKER-ITP13::NOT-MEMBER-REMOVE-CONFLICTING-LITERALS))
 (36 5 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS3))
 (16 16 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::REMOVE-CONFLICTING-LITERALS))
 (15 3 (:DEFINITION BINARY-APPEND))
 (12 12 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (10 6 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (10 6 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (10 2 (:REWRITE PROOF-CHECKER-ITP13::LITERALP-NEGATE))
 (8 8 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (8 8 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (6 6 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (6 6 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (6 2 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (6 1 (:REWRITE PROOF-CHECKER-ITP13::NEGATE-NEGATE))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (4 2 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (4 2 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 )
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-EXTEND-SHORT-ASSIGNMENT
 (43226 364 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (42884 1092 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (41154 1220 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (36397 96 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP))
 (36109 96 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (28836 96 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-CDR))
 (22036 96 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))
 (9738 8178 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (9296 9296 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (8938 8938 (:REWRITE DEFAULT-CAR))
 (8874 8874 (:REWRITE DEFAULT-CDR))
 (8277 8277 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (4236 4236 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (3399 99 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS2))
 (2319 2319 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (1092 1092 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (1051 99 (:REWRITE PROOF-CHECKER-ITP13::NOT-MEMBER-REMOVE-CONFLICTING-LITERALS))
 (936 52 (:DEFINITION PROOF-CHECKER-ITP13::REMOVE-CONFLICTING-LITERALS))
 (723 99 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-REMOVE-CONFLICTING-LITERALS3))
 (354 354 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (300 50 (:REWRITE PROOF-CHECKER-ITP13::LITERALP-IMPLIES-NOT-EQUAL-NEGATE))
 (260 52 (:DEFINITION BINARY-APPEND))
 (220 220 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 (220 220 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (215 43 (:REWRITE PROOF-CHECKER-ITP13::LITERALP-NEGATE))
 (177 177 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (168 28 (:REWRITE PROOF-CHECKER-ITP13::NEGATE-NEGATE))
 (96 96 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (96 96 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 (85 85 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (54 54 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 )
(PROOF-CHECKER-ITP13::SUBSETP-LIST-TRUEP-EVALUATE-FORMULA-EXTEND-SHORT-ASSIGNMENT
 (63180 1755 (:REWRITE PROOF-CHECKER-ITP13::NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP))
 (63180 585 (:DEFINITION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (57915 1755 (:DEFINITION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (57915 195 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP))
 (57330 195 (:DEFINITION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (53547 78 (:DEFINITION PROOF-CHECKER-ITP13::SUBSETP))
 (53352 195 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-CDR))
 (34263 4976 (:DEFINITION MEMBER-EQUAL))
 (28860 195 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))
 (14040 14040 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-DIFFERENCE-VARIABLES))
 (11711 11711 (:REWRITE DEFAULT-CDR))
 (11690 11690 (:REWRITE DEFAULT-CAR))
 (9952 9952 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (9952 9952 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (7472 7472 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6377 109 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (4898 4898 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (4898 4898 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (3900 3900 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SUBSET-VARIABLESP))
 (2453 109 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (1755 1755 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-TRANSITIVE))
 (195 195 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP))
 (195 195 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 (164 164 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::EXTEND-SHORT-ASSIGNMENT))
 (109 109 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (109 109 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (36 36 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-TRUE))
 )
(PROOF-CHECKER-ITP13::TRUEP-EVALUATE-FORMULA-EXTEND-SHORT-ASSIGNMENT
 (380 2 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-FORMULA))
 (227 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (211 37 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (196 34 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (126 35 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (121 8 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-EXTEND-SHORT-ASSIGNMENT))
 (88 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (56 8 (:DEFINITION MEMBER-EQUAL))
 (52 52 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-CLAUSE))
 (39 18 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (32 20 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (32 18 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (32 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-FALSEP))
 (26 14 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (24 24 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA))
 (23 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-UNDEFP))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (16 16 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (4 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::EXTEND-SHORT-ASSIGNMENT))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 )
(PROOF-CHECKER-ITP13::STRONG-ASSIGNMENT-EXTEND-SHORT-ASSIGNMENT
 (380 2 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-FORMULA))
 (227 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (211 37 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (196 34 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (126 35 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (121 8 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-EXTEND-SHORT-ASSIGNMENT))
 (96 1 (:DEFINITION PROOF-CHECKER-ITP13::FORMULAP))
 (88 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (81 1 (:DEFINITION PROOF-CHECKER-ITP13::CLAUSEP))
 (77 11 (:DEFINITION MEMBER-EQUAL))
 (52 52 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-CLAUSE))
 (39 18 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (32 20 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (32 18 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (32 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-FALSEP))
 (27 6 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CONJUNCTION))
 (26 14 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (25 1 (:DEFINITION PROOF-CHECKER-ITP13::LITERAL-LISTP))
 (24 24 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA))
 (24 1 (:DEFINITION PROOF-CHECKER-ITP13::NO-CONFLICTING-LITERALSP))
 (23 23 (:REWRITE DEFAULT-CDR))
 (23 14 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-UNDEFP))
 (22 22 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (22 22 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (21 21 (:REWRITE DEFAULT-CAR))
 (18 1 (:DEFINITION PROOF-CHECKER-ITP13::UNIQUE-LITERALSP))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (13 1 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-LITERALP-MEMBER))
 (10 10 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (10 10 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (9 3 (:REWRITE PROOF-CHECKER-ITP13::ASSIGNMENTP-CDR))
 (9 2 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-LIST-TRUEP-EVALUATE-FORMULA-EXTEND-SHORT-ASSIGNMENT))
 (4 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::EXTEND-SHORT-ASSIGNMENT))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (4 1 (:REWRITE PROOF-CHECKER-ITP13::FORMULAP-IMPLIES-CLAUSEP-CAR))
 (4 1 (:REWRITE PROOF-CHECKER-ITP13::FORMULAP-CDR))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-NOT-SUBSETP-IMPLIES-NOT-NO-CONFLICTING-LITERALSP))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 (2 2 (:REWRITE PROOF-CHECKER-ITP13::NOT-NO-CONFLICTING-LITERALSP))
 (1 1 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NO-CONFLICTING-LITERALSP))
 (1 1 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::LITERALP))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::LITERAL-LISTP-IMPLIES-LITERALP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::FORMULAP-MEMBER))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::CLAUSEP-MEMBER))
 )
(PROOF-CHECKER-ITP13::EXISTS-STRONG-SATISFYING-ASSIGNMENT)
(PROOF-CHECKER-ITP13::EXISTS-STRONG-SATISFYING-ASSIGNMENT-SUFF)
(PROOF-CHECKER-ITP13::SATISFYING-ASSIGNMENT-IMPLIES-EXISTS-STRONG-SATISFYING-ASSIGNMENT
 (1102 4 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-FORMULA))
 (808 14 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-CLAUSE))
 (564 93 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-UNDEF))
 (495 29 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-SHORTEN-LONG-ASSIGNMENT))
 (429 95 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-TRUE-NOT-FALSE))
 (416 77 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-NOT-FALSE-NOT-UNDEF))
 (322 14 (:DEFINITION PROOF-CHECKER-ITP13::EVALUATE-LITERAL))
 (261 8 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-EVALUATE-CLAUSE-EXTEND-SHORT-ASSIGNMENT))
 (210 28 (:DEFINITION MEMBER-EQUAL))
 (158 158 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-CLAUSE))
 (94 40 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-TRUEP))
 (82 40 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-TRUEP))
 (73 49 (:REWRITE PROOF-CHECKER-ITP13::FALSEP-IMPLIES-NOT-UNDEFP))
 (64 28 (:REWRITE PROOF-CHECKER-ITP13::UNDEFP-IMPLIES-NOT-FALSEP))
 (56 56 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-MEMBER-IMPLIES-MEMBER))
 (56 56 (:REWRITE PROOF-CHECKER-ITP13::MEMBER-UNION-VARIABLES1))
 (53 28 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-FALSEP))
 (51 31 (:REWRITE PROOF-CHECKER-ITP13::TRUEP-IMPLIES-NOT-UNDEFP))
 (46 46 (:REWRITE DEFAULT-CDR))
 (46 46 (:REWRITE DEFAULT-CAR))
 (28 28 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::NEGATE))
 (28 28 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (28 28 (:REWRITE PROOF-CHECKER-ITP13::SUBSET-VARIABLESP-IMPLIES-MEMBER-OR-MEMBER-NEGATE))
 (24 24 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::SHORTEN-LONG-ASSIGNMENT))
 (19 19 (:REWRITE PROOF-CHECKER-ITP13::TERNARYP-EVALUATE-FORMULA))
 (17 2 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-LIST-TRUEP-EVALUATE-FORMULA-EXTEND-SHORT-ASSIGNMENT))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-LITERAL))
 (14 14 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-CLAUSE))
 (8 4 (:TYPE-PRESCRIPTION PROOF-CHECKER-ITP13::EXTEND-SHORT-ASSIGNMENT))
 (8 1 (:REWRITE PROOF-CHECKER-ITP13::SUBSETP-LIST-TRUEP-EVALUATE-FORMULA-SHORTEN-LONG-ASSIGNMENT))
 (4 4 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUALP-IMPLIES-EQUAL-EVALUATE-FORMULA))
 (1 1 (:REWRITE PROOF-CHECKER-ITP13::SET-EQUAL-VARIABLESP-TRANSITIVE))
 )
