(BAG::NEQ)
(BAG::FOO)
(BAG::FIND-MEMBERP-LITERAL-THAT-SHOWS-A-AND-B-DIFFER-FN
 (2790 30 (:REWRITE LIST::EQUAL-OF-IF-HACK))
 (2250 300 (:DEFINITION LEN))
 (1057 1057 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (1050 600 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (1020 90 (:LINEAR LIST::LEN-LINEAR))
 (995 965 (:REWRITE DEFAULT-CDR))
 (810 30 (:LINEAR LIST::LEN-OF-CDR-LINEAR))
 (664 574 (:REWRITE DEFAULT-CAR))
 (660 330 (:REWRITE DEFAULT-+-2))
 (440 224 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (420 90 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (330 330 (:REWRITE DEFAULT-+-1))
 (226 64 (:DEFINITION TRUE-LISTP))
 (224 224 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (224 224 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (128 128 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP-CHEAP))
 (120 30 (:DEFINITION SYMBOL-LISTP))
 (96 96 (:TYPE-PRESCRIPTION BOOLEANP))
 (90 90 (:LINEAR SYN::LEN-IMPLIES-ACL2-LEN))
 (86 86 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (80 80 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (60 30 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (24 24 (:REWRITE BAG::HACK-ERIC))
 )
(BAG::FIND-MEMBERP-LITERAL-THAT-SHOWS-A-AND-B-DIFFER-IRRELEVANT
 (263 263 (:REWRITE DEFAULT-CDR))
 (168 168 (:REWRITE DEFAULT-CAR))
 (120 57 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (58 58 (:REWRITE BAG::HACK-ERIC))
 (57 57 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (57 57 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (57 4 (:REWRITE LIST::EQUAL-OF-IF-HACK))
 (47 47 (:TYPE-PRESCRIPTION BOOLEANP))
 (46 46 (:REWRITE LIST::LEN-FW-TO-CONSP))
 )
(BAG::METAFUNCTION-TO-REWRITE-EQUAL-TO-NIL
 (465 5 (:REWRITE LIST::EQUAL-OF-IF-HACK))
 (375 50 (:DEFINITION LEN))
 (215 15 (:DEFINITION LENGTH))
 (190 190 (:TYPE-PRESCRIPTION LEN))
 (175 100 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (172 167 (:REWRITE DEFAULT-CDR))
 (170 15 (:LINEAR LIST::LEN-LINEAR))
 (167 167 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (135 5 (:LINEAR LIST::LEN-OF-CDR-LINEAR))
 (110 55 (:REWRITE DEFAULT-+-2))
 (99 84 (:REWRITE DEFAULT-CAR))
 (70 15 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (63 29 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (55 55 (:REWRITE DEFAULT-+-1))
 (36 36 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP-CHEAP))
 (29 29 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (29 29 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (24 8 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (21 21 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (20 5 (:DEFINITION SYMBOL-LISTP))
 (19 19 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 15 (:LINEAR SYN::LEN-IMPLIES-ACL2-LEN))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (10 5 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(BAG::HYP-FOR-METAFUNCTION-TO-REWRITE-EQUAL-TO-NIL
 (372 4 (:REWRITE LIST::EQUAL-OF-IF-HACK))
 (300 40 (:DEFINITION LEN))
 (172 12 (:DEFINITION LENGTH))
 (152 152 (:TYPE-PRESCRIPTION LEN))
 (142 138 (:REWRITE DEFAULT-CDR))
 (140 80 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (136 12 (:LINEAR LIST::LEN-LINEAR))
 (133 133 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (108 4 (:LINEAR LIST::LEN-OF-CDR-LINEAR))
 (88 44 (:REWRITE DEFAULT-+-2))
 (80 68 (:REWRITE DEFAULT-CAR))
 (56 12 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (50 23 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (44 44 (:REWRITE DEFAULT-+-1))
 (26 26 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP-CHEAP))
 (23 23 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (23 23 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (18 18 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (18 6 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (16 16 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 4 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:LINEAR SYN::LEN-IMPLIES-ACL2-LEN))
 (11 11 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(APPLY-FOR-DEFEVALUATOR)
(BAG::EV3)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(BAG::EV3-CONSTRAINT-0)
(BAG::EV3-CONSTRAINT-1)
(BAG::EV3-CONSTRAINT-2)
(BAG::EV3-CONSTRAINT-3)
(BAG::EV3-CONSTRAINT-4)
(BAG::EV3-CONSTRAINT-5)
(BAG::EV3-CONSTRAINT-6)
(BAG::EV3-CONSTRAINT-7)
(BAG::EV3-CONSTRAINT-8)
(BAG::EV3-CONSTRAINT-9)
(BAG::EV3-CONSTRAINT-10)
(BAG::EV3-CONSTRAINT-11)
(BAG::EV3-CONSTRAINT-12)
(BAG::EV3-CONSTRAINT-13)
(BAG::SYNTACTIC-MEMBERSHIP-META-RULE-HELPER
 (737 16 (:DEFINITION BAG::MEMBERP))
 (607 40 (:REWRITE BAG::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (362 362 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (270 190 (:REWRITE DEFAULT-CDR))
 (227 15 (:REWRITE BAG::SUBBAGP-CDR-LEMMA))
 (140 108 (:REWRITE DEFAULT-CAR))
 (122 54 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (105 6 (:REWRITE BAG::SUBBAGP-IMPLIES-MEMBERSHIP))
 (87 6 (:REWRITE BAG::SUBBAGP-OF-CDR))
 (80 40 (:REWRITE BAG::MEMBERP-OF-CDR-CHEAP))
 (78 6 (:REWRITE BAG::MEMBERP-CAR-WHEN-DISJOINT))
 (54 54 (:TYPE-PRESCRIPTION BOOLEANP))
 (54 54 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (54 54 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (54 6 (:REWRITE BAG::NON-UNIQUE-NOT-SUBBAGP-OF-UNIQUE))
 (49 28 (:REWRITE BAG::EV3-CONSTRAINT-13))
 (49 28 (:REWRITE BAG::EV3-CONSTRAINT-12))
 (49 28 (:REWRITE BAG::EV3-CONSTRAINT-11))
 (48 15 (:REWRITE BAG::SUBBAGP-WHEN-CDR-IS-NON-CONSP))
 (45 24 (:REWRITE BAG::EV3-CONSTRAINT-8))
 (45 24 (:REWRITE BAG::EV3-CONSTRAINT-3))
 (44 44 (:REWRITE BAG::NON-MEMBERP-COMPUTATION))
 (44 44 (:REWRITE BAG::MEMBERP-COMPUTATION))
 (44 44 (:META BAG::META-RULE-TO-SIMPLIFY-CONS-AND-APPEND-NEST))
 (43 43 (:REWRITE BAG::MEMBERP-OF-REMOVE-BAG-MEANS-MEMBERP))
 (43 43 (:REWRITE BAG::MEMBERP-OF-REMOVE-ALL))
 (43 43 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINTNESS))
 (43 43 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-TWO))
 (43 43 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-ONE))
 (40 40 (:REWRITE BAG::MEMBERP-OF-REMOVE-1))
 (40 40 (:REWRITE BAG::MEMBERP-OF-NON-CONSP-CHEAP))
 (33 15 (:REWRITE BAG::SUBBAGP-OF-NON-CONSP-TWO-CHEAP))
 (33 3 (:REWRITE BAG::DISJOINT-CDR-FROM-DISJOINT))
 (24 24 (:REWRITE BAG::HACK-ERIC))
 (23 1 (:REWRITE LIST::APPEND-EQUAL-SELF-ONE))
 (22 22 (:REWRITE BAG::EV3-CONSTRAINT-1))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (18 18 (:REWRITE BAG::BIND-SUBBAGP-REMOVE-BAG))
 (18 6 (:REWRITE LIST::EQUAL-CAR-DIFFERENTIAL))
 (16 8 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (16 8 (:TYPE-PRESCRIPTION LIST::APPEND-TRUE-LISTP-TYPE-PRESCRIPTION-BETTER))
 (15 15 (:REWRITE BAG::SUBBAGP-REMOVE-BAG))
 (15 15 (:REWRITE BAG::SUBBAGP-REMOVE))
 (15 15 (:REWRITE BAG::SUBBAGP-OF-REMOVE-1-IMPLIES-SUBBAGP))
 (15 15 (:REWRITE BAG::SUBBAGP-CHAINING))
 (12 12 (:TYPE-PRESCRIPTION BAG::UNIQUE))
 (12 6 (:REWRITE BAG::MEMBERP-CAR-WHEN-DISJOINT-CHEAP))
 (11 7 (:REWRITE BAG::DISJOINT-OF-NON-CONSP-TWO))
 (11 1 (:REWRITE LIST::FINAL-CDR-WHEN-TRUE-LISTP))
 (9 6 (:REWRITE BAG::SUBBAGP-OF-NON-CONSP-TWO))
 (9 6 (:REWRITE BAG::SUBBAGP-OF-NON-CONSP-ONE))
 (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (8 8 (:TYPE-PRESCRIPTION LIST::APPEND-CONSP-TYPE-TWO))
 (8 8 (:TYPE-PRESCRIPTION LIST::APPEND-CONSP-TYPE-ONE))
 (7 7 (:REWRITE BAG::SUBBAGP-DISJOINT-COMMUTE))
 (7 7 (:REWRITE BAG::SUBBAGP-DISJOINT))
 (7 7 (:REWRITE BAG::DISJOINT-OTHER-MEMBERP))
 (7 7 (:REWRITE BAG::DISJOINT-FROM-COMMON-UNIQUENSS))
 (7 7 (:REWRITE BAG::DISJOINT-COMPUTATION))
 (7 1 (:DEFINITION TRUE-LISTP))
 (6 6 (:REWRITE BAG::UNIQUE-SUBBAGP-UNIQUE-FREE))
 (6 6 (:REWRITE BAG::UNIQUE-OF-NON-CONSP-CHEAP))
 (6 6 (:REWRITE BAG::UNIQUE-IF-PERM-OF-SOMETHING-UNIQUE))
 (6 6 (:REWRITE BAG::UNIQUE-COMPUTATION))
 (6 6 (:REWRITE BAG::SUBBAGP-UNIQUENESS))
 (6 6 (:REWRITE BAG::SUBBAGP-OF-NON-CONSP-ONE-CHEAP))
 (6 6 (:REWRITE BAG::SUBBAGP-NIL-FROM-<-OF-COUNTS))
 (6 6 (:REWRITE BAG::SUBBAGP-FALSE-FROM-WITNESS))
 (6 6 (:REWRITE BAG::*TRIGGER*-SYNTAX-EV-SYNTAX-SUBBAGP))
 (6 3 (:REWRITE BAG::DISJOINT-CDR-FROM-DISJOINT-CHEAP))
 (4 2 (:REWRITE LIST::APPEND-OF-NON-CONSP-ONE))
 (4 1 (:REWRITE LIST::APPEND-EQUAL-SELF-TWO))
 (3 3 (:TYPE-PRESCRIPTION LIST::FINAL-CDR))
 (2 2 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP-CHEAP))
 (2 1 (:REWRITE LIST::FINAL-CDR-WHEN-NON-CONSP))
 (2 1 (:REWRITE LIST::FINAL-CDR-WHEN-CDR-NOT-CONSP))
 )
(BAG::HELPER-BOZO
 (297 297 (:REWRITE DEFAULT-CDR))
 (294 294 (:REWRITE DEFAULT-CAR))
 (251 251 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (243 128 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (140 34 (:REWRITE BAG::EV3-CONSTRAINT-9))
 (140 34 (:REWRITE BAG::EV3-CONSTRAINT-13))
 (140 34 (:REWRITE BAG::EV3-CONSTRAINT-12))
 (140 34 (:REWRITE BAG::EV3-CONSTRAINT-11))
 (140 34 (:REWRITE BAG::EV3-CONSTRAINT-10))
 (138 32 (:REWRITE BAG::EV3-CONSTRAINT-2))
 (128 128 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (128 128 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (115 115 (:TYPE-PRESCRIPTION BOOLEANP))
 (98 32 (:REWRITE BAG::EV3-CONSTRAINT-3))
 (56 32 (:REWRITE BAG::EV3-CONSTRAINT-1))
 (42 4 (:REWRITE BAG::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (40 40 (:REWRITE BAG::HACK-ERIC))
 (8 4 (:REWRITE BAG::MEMBERP-OF-CDR-CHEAP))
 (4 4 (:REWRITE BAG::NON-MEMBERP-COMPUTATION))
 (4 4 (:REWRITE BAG::MEMBERP-SUBBAGP))
 (4 4 (:REWRITE BAG::MEMBERP-OF-REMOVE-BAG-MEANS-MEMBERP))
 (4 4 (:REWRITE BAG::MEMBERP-OF-REMOVE-ALL))
 (4 4 (:REWRITE BAG::MEMBERP-OF-REMOVE-1))
 (4 4 (:REWRITE BAG::MEMBERP-OF-NON-CONSP-CHEAP))
 (4 4 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINTNESS))
 (4 4 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-TWO))
 (4 4 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-ONE))
 (4 4 (:REWRITE BAG::MEMBERP-COMPUTATION))
 (4 4 (:META BAG::SYNTACTIC-MEMBERSHIP-META-RULE))
 (4 4 (:META BAG::META-RULE-TO-SIMPLIFY-CONS-AND-APPEND-NEST))
 (2 1 (:REWRITE BAG::DISJOINT-OF-NON-CONSP-TWO))
 (1 1 (:REWRITE BAG::SUBBAGP-DISJOINT-COMMUTE))
 (1 1 (:REWRITE BAG::SUBBAGP-DISJOINT))
 (1 1 (:REWRITE BAG::DISJOINT-OTHER-MEMBERP))
 (1 1 (:REWRITE BAG::DISJOINT-FROM-COMMON-UNIQUENSS))
 (1 1 (:REWRITE BAG::DISJOINT-COMPUTATION))
 )
(BAG::META-RULE-TO-REWRITE-EQUAL-TO-NIL
 (3395 3091 (:REWRITE DEFAULT-CDR))
 (1628 1628 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (870 680 (:REWRITE DEFAULT-CAR))
 (516 185 (:REWRITE BAG::EV3-CONSTRAINT-12))
 (452 157 (:REWRITE BAG::EV3-CONSTRAINT-9))
 (452 157 (:REWRITE BAG::EV3-CONSTRAINT-8))
 (452 157 (:REWRITE BAG::EV3-CONSTRAINT-10))
 (441 203 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (360 157 (:REWRITE BAG::EV3-CONSTRAINT-3))
 (203 203 (:TYPE-PRESCRIPTION BOOLEANP))
 (203 203 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (203 203 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (158 158 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP-CHEAP))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(BAG::NEQ-TEST-1)
(BAG::NEQ-TEST-2)
(BAG::NEQ-TEST-2-ALT)
(BAG::FIND-NEGATED-MEMBERP-LITERAL-IN-CLAUSE)
(BAG::FIND-TWO-MEMBERP-LITERALS-THAT-TELL-YOU-THAT-A-AND-B-DIFFER)
(BAG::METAFUNCTION-FOR-TWO-MEMBERP-LITERALS-BLAH)
(BAG::HYP-METAFUNCTION-FOR-TWO-MEMBERP-LITERALS-BLAH)
(BAG::CONS-IFF)
(BAG::HELPER3
 (265 265 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (177 177 (:REWRITE DEFAULT-CAR))
 (175 175 (:REWRITE DEFAULT-CDR))
 (129 37 (:REWRITE BAG::EV3-CONSTRAINT-9))
 (129 37 (:REWRITE BAG::EV3-CONSTRAINT-13))
 (129 37 (:REWRITE BAG::EV3-CONSTRAINT-12))
 (129 37 (:REWRITE BAG::EV3-CONSTRAINT-11))
 (129 37 (:REWRITE BAG::EV3-CONSTRAINT-10))
 (128 36 (:REWRITE BAG::EV3-CONSTRAINT-2))
 (118 36 (:REWRITE BAG::EV3-CONSTRAINT-3))
 (86 56 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (63 6 (:REWRITE BAG::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (56 56 (:META BAG::META-RULE-TO-REWRITE-EQUAL-TO-NIL))
 (56 56 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (56 56 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (30 30 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 6 (:REWRITE BAG::MEMBERP-OF-CDR-CHEAP))
 (6 6 (:REWRITE BAG::NON-MEMBERP-COMPUTATION))
 (6 6 (:REWRITE BAG::MEMBERP-SUBBAGP))
 (6 6 (:REWRITE BAG::MEMBERP-OF-REMOVE-BAG-MEANS-MEMBERP))
 (6 6 (:REWRITE BAG::MEMBERP-OF-REMOVE-ALL))
 (6 6 (:REWRITE BAG::MEMBERP-OF-REMOVE-1))
 (6 6 (:REWRITE BAG::MEMBERP-OF-NON-CONSP-CHEAP))
 (6 6 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINTNESS))
 (6 6 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-TWO))
 (6 6 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-ONE))
 (6 6 (:REWRITE BAG::MEMBERP-COMPUTATION))
 (6 6 (:REWRITE BAG::BIND-MEMBERP-REMOVE-BAG))
 (6 6 (:META BAG::SYNTACTIC-MEMBERSHIP-META-RULE))
 (6 6 (:META BAG::META-RULE-TO-SIMPLIFY-CONS-AND-APPEND-NEST))
 )
(BAG::SYNTACTIC-MEMBERSHIP-META-RULE-HELPER-2
 (1309 1309 (:REWRITE DEFAULT-CDR))
 (801 801 (:REWRITE DEFAULT-CAR))
 (613 391 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (575 575 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (522 58 (:REWRITE LIST::EQUAL-CAR-DIFFERENTIAL))
 (391 391 (:META BAG::META-RULE-TO-REWRITE-EQUAL-TO-NIL))
 (391 391 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (391 391 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (222 222 (:TYPE-PRESCRIPTION BOOLEANP))
 (184 44 (:REWRITE BAG::EV3-CONSTRAINT-13))
 (172 40 (:REWRITE BAG::EV3-CONSTRAINT-9))
 (172 40 (:REWRITE BAG::EV3-CONSTRAINT-10))
 (150 4 (:DEFINITION BAG::MEMBERP))
 (144 10 (:REWRITE BAG::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (110 38 (:REWRITE BAG::EV3-CONSTRAINT-3))
 (60 36 (:REWRITE BAG::EV3-CONSTRAINT-1))
 (20 10 (:REWRITE BAG::MEMBERP-OF-CDR-CHEAP))
 (10 10 (:REWRITE BAG::NON-MEMBERP-COMPUTATION))
 (10 10 (:REWRITE BAG::MEMBERP-SUBBAGP))
 (10 10 (:REWRITE BAG::MEMBERP-OF-REMOVE-BAG-MEANS-MEMBERP))
 (10 10 (:REWRITE BAG::MEMBERP-OF-REMOVE-ALL))
 (10 10 (:REWRITE BAG::MEMBERP-OF-REMOVE-1))
 (10 10 (:REWRITE BAG::MEMBERP-OF-NON-CONSP-CHEAP))
 (10 10 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINTNESS))
 (10 10 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-TWO))
 (10 10 (:REWRITE BAG::MEMBERP-FALSE-FROM-DISJOINT-OF-CONS-ONE))
 (10 10 (:REWRITE BAG::MEMBERP-COMPUTATION))
 (10 10 (:REWRITE BAG::BIND-MEMBERP-REMOVE-BAG))
 (10 10 (:META BAG::SYNTACTIC-MEMBERSHIP-META-RULE))
 (10 10 (:META BAG::META-RULE-TO-SIMPLIFY-CONS-AND-APPEND-NEST))
 (4 4 (:REWRITE BAG::HELPER-BOZO))
 )
(BAG::META-RULE-FOR-TWO-MEMBERP-LITERALS
 (2956 2709 (:REWRITE DEFAULT-CDR))
 (732 732 (:REWRITE LIST::LEN-FW-TO-CONSP))
 (512 376 (:REWRITE DEFAULT-CAR))
 (153 80 (:REWRITE LIST::EQUAL-OF-BOOLEANS-REWRITE))
 (148 148 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP-CHEAP))
 (128 14 (:REWRITE LIST::EQUAL-CAR-DIFFERENTIAL))
 (105 47 (:REWRITE BAG::EV3-CONSTRAINT-9))
 (105 47 (:REWRITE BAG::EV3-CONSTRAINT-8))
 (105 47 (:REWRITE BAG::EV3-CONSTRAINT-12))
 (105 47 (:REWRITE BAG::EV3-CONSTRAINT-11))
 (105 47 (:REWRITE BAG::EV3-CONSTRAINT-10))
 (83 47 (:REWRITE BAG::EV3-CONSTRAINT-3))
 (80 80 (:META BAG::META-RULE-TO-REWRITE-EQUAL-TO-NIL))
 (80 80 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (80 80 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (59 59 (:TYPE-PRESCRIPTION BOOLEANP))
 (56 14 (:DEFINITION BAG::FIND-NEGATED-MEMBERP-LITERAL-IN-CLAUSE))
 (38 36 (:REWRITE BAG::EV3-CONSTRAINT-1))
 (20 20 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (9 9 (:REWRITE BAG::HELPER-BOZO))
 (4 4 (:REWRITE BAG::CONS-IFF))
 )
(BAG::TEST-META-RULE-FOR-TWO-MEMBERP-LITERALS)
