(EXPT-OF-+-OF-1-LINEAR
 (15 15 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 1 (:REWRITE DEFAULT-*-2))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(EXPT-OF-+-OF--1-LINEAR
 (46 46 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (34 1 (:LINEAR EXPT-HALF-LINEAR))
 (16 4 (:REWRITE DEFAULT-*-2))
 (7 4 (:REWRITE DEFAULT-+-2))
 (7 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(EXPT-OF-+-OF--1-LINEAR-2
 (68 2 (:LINEAR EXPT-HALF-LINEAR))
 (56 56 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (32 8 (:REWRITE DEFAULT-*-2))
 (20 11 (:REWRITE DEFAULT-+-2))
 (20 11 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEFAULT-*-1))
 (8 8 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE EQUAL-OF-EXPT-AND-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(BVNOT-BECOMES-BVPLUS-OF--1-AND-BVUMINUS
 (291 6 (:REWRITE BVCHOP-IDENTITY))
 (250 5 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (84 8 (:DEFINITION NATP))
 (84 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (78 78 (:TYPE-PRESCRIPTION IFIX))
 (62 18 (:REWRITE DEFAULT-<-2))
 (40 13 (:REWRITE DEFAULT-+-2))
 (40 13 (:REWRITE DEFAULT-+-1))
 (40 4 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (38 38 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (38 38 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (36 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (32 4 (:REWRITE <-OF-+-OF---AND-0-ARG1))
 (22 22 (:META CANCEL_PLUS-LESSP-CORRECT))
 (22 18 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION NATP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (11 11 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (11 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (10 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (10 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (8 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (6 6 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR))
 (6 2 (:REWRITE --OF--))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (5 5 (:REWRITE UBP-LONGER-BETTER))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 5 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (5 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 )
(UNSIGNED-BYTE-P-OF-+-OF-1-AND-+
 (24 24 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (11 5 (:REWRITE DEFAULT-<-2))
 (7 4 (:REWRITE DEFAULT-+-2))
 (7 4 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(BVPLUS-OF-+-OF-1-SPLIT
 (235 235 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (235 235 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (185 3 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (60 23 (:REWRITE DEFAULT-+-2))
 (49 23 (:REWRITE DEFAULT-+-1))
 (48 3 (:DEFINITION NATP))
 (37 9 (:REWRITE DEFAULT-<-2))
 (36 36 (:TYPE-PRESCRIPTION IFIX))
 (28 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (18 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (16 9 (:REWRITE DEFAULT-<-1))
 (15 5 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (15 3 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (10 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (9 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (9 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (6 6 (:REWRITE UBP-LONGER-BETTER))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR))
 (6 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (5 5 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE +-COMBINE-CONSTANTS))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (3 3 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (3 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (2 2 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (2 2 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 )
(<-OF-EXPT-CANCEL-1
 (80 32 (:REWRITE DEFAULT-+-2))
 (68 32 (:REWRITE DEFAULT-+-1))
 (48 48 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (20 8 (:REWRITE DEFAULT-<-2))
 (14 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (8 8 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (6 6 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE +-COMBINE-CONSTANTS))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(ONES-COMPLEMENT)
(UNSIGNED-BYTE-P-OF-ONES-COMPLEMENT
 (9 1 (:REWRITE BVNOT-WHEN-NOT-NATP-SIZE))
 (7 4 (:REWRITE DEFAULT-<-2))
 (7 1 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-POSITIVE))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 3 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (3 3 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 1 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-INTEGERP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(FROM-ONES-COMPLEMENT
 (272 272 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (24 5 (:REWRITE DEFAULT-<-2))
 (13 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (4 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (4 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(REPRESENTABLE-AS-ONES-COMPLEMENTP
 (42 42 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 )
(REPRESENTABLE-AS-ONES-COMPLEMENTP-FROM-ONES-COMPLEMENT
 (263 77 (:REWRITE DEFAULT-+-2))
 (128 77 (:REWRITE DEFAULT-+-1))
 (76 25 (:REWRITE DEFAULT-<-2))
 (64 25 (:REWRITE DEFAULT-<-1))
 (47 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 25 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (12 12 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (10 10 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (10 10 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (10 10 (:REWRITE UBP-LONGER-BETTER))
 (8 2 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (7 7 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (6 6 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (5 5 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (4 1 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (1 1 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
 (1 1 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-POSITIVE))
 (1 1 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-INTEGERP))
 (1 1 (:REWRITE BVNOT-WHEN-NOT-NATP-SIZE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (1 1 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (1 1 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 )
(TO-ONES-COMPLEMENT)
(BVNOT-OF-+-OF-1-AND-EXPT-SAME
 (208 5 (:REWRITE BVCHOP-IDENTITY))
 (170 3 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (48 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (36 12 (:REWRITE DEFAULT-<-2))
 (36 9 (:REWRITE DEFAULT-+-2))
 (33 33 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (31 1 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (25 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (24 9 (:REWRITE DEFAULT-+-1))
 (23 1 (:REWRITE <-OF-+-OF---AND-0-ARG2))
 (21 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (20 20 (:TYPE-PRESCRIPTION IFIX))
 (20 12 (:REWRITE DEFAULT-<-1))
 (17 2 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (16 16 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (16 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (15 15 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (11 8 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (10 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:LINEAR EXPT-BOUND-LINEAR))
 (8 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG2))
 (8 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (6 6 (:REWRITE UBP-LONGER-BETTER))
 (6 6 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (6 6 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (6 3 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (6 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (6 3 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (5 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (4 4 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (3 3 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (3 3 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (3 3 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (3 1 (:REWRITE --OF--))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (2 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (2 1 (:REWRITE <-OF-1-AND-EXPT))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(BVCHOP-WHEN-NEGATIVE-AND-SMALL
 (2426 12 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (1280 13 (:REWRITE MOD-IS-0-WHEN-MULTIPLE))
 (900 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (399 17 (:REWRITE FLOOR-WHEN-<=))
 (392 16 (:REWRITE FLOOR-WHEN-<))
 (384 13 (:REWRITE MOD-WHEN-MULTIPLE))
 (384 13 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (352 59 (:REWRITE DEFAULT-*-2))
 (348 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (339 27 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (339 17 (:REWRITE FLOOR-MUST-BE-1))
 (338 4 (:REWRITE EQUAL-OF-0-AND-+-OF--))
 (316 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (304 90 (:REWRITE DEFAULT-<-2))
 (304 24 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (273 31 (:REWRITE DEFAULT-UNARY-/))
 (264 24 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (264 13 (:REWRITE MOD-WHEN-<))
 (243 90 (:REWRITE DEFAULT-<-1))
 (207 59 (:REWRITE DEFAULT-*-1))
 (185 25 (:REWRITE DEFAULT-+-2))
 (183 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (151 17 (:REWRITE FLOOR-WHEN-MOD-0-CHEAP))
 (151 17 (:REWRITE FLOOR-WHEN-DIVISIBLE-CHEAP))
 (136 24 (:REWRITE INTEGERP-OF-*))
 (120 120 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (120 24 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (104 104 (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
 (104 104 (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
 (100 17 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (92 92 (:META CANCEL_PLUS-LESSP-CORRECT))
 (76 13 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (64 13 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (64 2 (:REWRITE <-OF-/-AND-CONSTANT))
 (50 25 (:REWRITE DEFAULT-+-1))
 (36 17 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (36 2 (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (34 34 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (32 16 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (32 16 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (25 13 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (25 13 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (24 24 (:REWRITE INTEGERP-OF-POWER2-HACK))
 (24 2 (:DEFINITION NATP))
 (22 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (22 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (17 17 (:REWRITE FLOOR-DIVIDE-BY-COMMON-CONSTANT-FACTOR))
 (16 16 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (13 13 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (13 13 (:REWRITE DIVISIBLE-WHEN-DIVISIBLE-BY-MULTIPLE))
 (12 12 (:REWRITE SAME-REMAINDER-WHEN-CLOSE-LEMMA))
 (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 10 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*))
 (4 4 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (4 4 (:LINEAR <=-OF-/-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (1 1 (:REWRITE *-OF---ARG1))
 )
(BVNOT-OF--
 (428 18 (:REWRITE MOD-WHEN-MULTIPLE))
 (428 18 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (278 38 (:REWRITE DEFAULT-UNARY-/))
 (198 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (178 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (163 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (130 34 (:REWRITE DEFAULT-*-2))
 (108 9 (:REWRITE INTEGERP-OF--))
 (86 28 (:REWRITE DEFAULT-+-2))
 (85 19 (:REWRITE INTEGERP-OF-*))
 (76 27 (:REWRITE DEFAULT-<-2))
 (66 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (64 34 (:REWRITE DEFAULT-*-1))
 (58 28 (:REWRITE DEFAULT-+-1))
 (54 6 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (54 6 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (53 27 (:REWRITE DEFAULT-<-1))
 (52 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (48 6 (:REWRITE COMMUTATIVITY-OF-*))
 (45 45 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (45 9 (:REWRITE UNICITY-OF-1))
 (42 42 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (36 8 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (35 3 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (34 8 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (34 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (30 6 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (18 18 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (13 13 (:REWRITE INTEGERP-OF-POWER2-HACK))
 (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (10 10 (:REWRITE *-OF---ARG1))
 (10 8 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (10 8 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (7 1 (:REWRITE MOD-OF-+-WHEN-MULT-ARG1-ALT-CHEAP))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (4 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (2 2 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2-TYPE))
 (1 1 (:REWRITE MOD-OF-+-SUBST-CONSTANT-ARG2))
 (1 1 (:REWRITE MOD-OF-+-SUBST-CONSTANT-ARG1))
 (1 1 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 )
(FROM-ONES-COMPLEMENT-OF-TO-ONES-COMPLEMENT
 (374 146 (:REWRITE DEFAULT-+-2))
 (281 146 (:REWRITE DEFAULT-+-1))
 (257 257 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (234 15 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (146 50 (:REWRITE DEFAULT-<-2))
 (126 50 (:REWRITE DEFAULT-<-1))
 (114 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (86 3 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (63 3 (:REWRITE <-OF---AND--))
 (56 8 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (56 8 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (48 14 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (18 3 (:REWRITE <-OF-1-AND-EXPT))
 (16 16 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (14 14 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (13 13 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (13 13 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (13 13 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (13 13 (:REWRITE UBP-LONGER-BETTER))
 (10 10 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (10 10 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (8 8 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (8 8 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (8 8 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (8 8 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (7 1 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (5 5 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (3 3 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (2 2 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (2 2 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (2 2 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-POSITIVE))
 (1 1 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-INTEGERP))
 (1 1 (:REWRITE BVNOT-WHEN-NOT-NATP-SIZE))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (1 1 (:REWRITE BVCHOP-BOUND))
 (1 1 (:DEFINITION NATP))
 )
(NEGATIVE-ZERO
 (4 4 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 )
(TO-ONES-COMPLEMENT-OF-FROM-ONES-COMPLEMENT
 (961 18 (:REWRITE BVCHOP-WHEN-NEGATIVE-AND-SMALL))
 (363 153 (:REWRITE DEFAULT-+-2))
 (339 4 (:REWRITE <-OF---AND--))
 (267 153 (:REWRITE DEFAULT-+-1))
 (163 1 (:REWRITE BVNOT-OF--))
 (102 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (77 32 (:REWRITE DEFAULT-<-1))
 (65 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (53 32 (:REWRITE DEFAULT-<-2))
 (34 34 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (27 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (18 3 (:REWRITE <-OF-1-AND-EXPT))
 (16 16 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (13 13 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (13 13 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (13 13 (:REWRITE UBP-LONGER-BETTER))
 (9 9 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (9 9 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (9 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7 7 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 5 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE EQUAL-OF-EXPT-AND-CONSTANT))
 (4 4 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (4 1 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (3 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP))
 (2 2 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
 (2 2 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-POSITIVE))
 (2 2 (:REWRITE BVNOT-WHEN-SIZE-IS-NOT-INTEGERP))
 (2 2 (:REWRITE BVNOT-WHEN-NOT-NATP-SIZE))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (2 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG2))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (1 1 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (1 1 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 )
(BVPLUS1C
 (326 326 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (40 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (24 9 (:REWRITE DEFAULT-<-2))
 (18 6 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 6 (:REWRITE UBP-LONGER-BETTER))
 (10 4 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (8 2 (:REWRITE <-OF-1-AND-EXPT))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 2 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (4 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (3 3 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE +-COMBINE-CONSTANTS))
 )
(UNSIGNED-BYTE-P-OF-BVPLUS1C
 (1107 27 (:REWRITE BVCHOP-IDENTITY))
 (776 1 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (389 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (352 12 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (298 6 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (236 6 (:LINEAR BVCHOP-UPPER-BOUND))
 (123 67 (:REWRITE DEFAULT-<-1))
 (121 67 (:REWRITE DEFAULT-<-2))
 (82 28 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (81 21 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (68 68 (:META CANCEL_PLUS-LESSP-CORRECT))
 (60 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (48 27 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (45 18 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (41 41 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (41 21 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (33 11 (:REWRITE DEFAULT-+-2))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (28 28 (:REWRITE UBP-LONGER-BETTER))
 (27 27 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (23 23 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (21 21 (:TYPE-PRESCRIPTION POSP))
 (21 21 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (21 21 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (21 21 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (21 21 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (18 18 (:LINEAR EXPT-BOUND-LINEAR))
 (15 11 (:REWRITE DEFAULT-+-1))
 (12 6 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (6 6 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (3 3 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE +-COMBINE-CONSTANTS))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (1 1 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (1 1 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 )
(BVPLUS1C-CORRECT
 (5492 1655 (:REWRITE DEFAULT-+-2))
 (3095 1655 (:REWRITE DEFAULT-+-1))
 (2824 495 (:REWRITE DEFAULT-<-1))
 (2277 25 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (2253 467 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (1868 56 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1868 56 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1614 1614 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (1605 20 (:REWRITE BVUMINUS-WHEN-BVCHOP-KNOWN-SUBST))
 (1532 24 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (1341 495 (:REWRITE DEFAULT-<-2))
 (983 380 (:REWRITE DEFAULT-UNARY-MINUS))
 (651 42 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (530 530 (:REWRITE FOLD-CONSTS-IN-+))
 (467 467 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (462 462 (:REWRITE UBP-LONGER-BETTER))
 (262 174 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (227 20 (:REWRITE BVPLUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (165 165 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (164 20 (:REWRITE BVUMINUS-WHEN-ARG-IS-NOT-AN-INTEGER))
 (164 20 (:REWRITE BVMINUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (144 60 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (85 85 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (70 70 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (68 68 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (67 67 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (67 67 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (56 56 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (56 56 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (56 56 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (56 56 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (52 52 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (49 49 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (49 49 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (43 43 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (23 23 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (20 20 (:REWRITE BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (20 20 (:REWRITE BVPLUS-WHEN-NOT-NATP-ARG1-CHEAP))
 (20 20 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG3))
 (20 20 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG2))
 (20 20 (:REWRITE BVPLUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (20 20 (:REWRITE BVPLUS-SUBST-VALUE-ALT))
 (20 20 (:REWRITE BVPLUS-SUBST-VALUE))
 (20 20 (:REWRITE BVMINUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (20 20 (:REWRITE BVMINUS-WHEN-SIZE-IS-NOT-INTEGERP))
 (20 20 (:REWRITE BVMINUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (20 20 (:REWRITE BVMINUS-SUBST-VALUE-ARG-3))
 (20 20 (:REWRITE BVMINUS-SUBST-VALUE-ARG-2))
 (10 10 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (10 10 (:REWRITE BVCHOP-BOUND))
 (8 8 (:REWRITE EQUAL-OF-EXPT-AND-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
 (1 1 (:REWRITE EQUAL-OF---AND-CONSTANT))
 )
(+-OF-*-OF-1/2-AND-*-OF-1/2-SAME)
(ONES-COMPLEMENT-ZEROP
 (6 6 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 )
(ONES-COMPLEMENT-EQUAL)
(BVPLUS1C-CORRECT-2
 (13800 5085 (:REWRITE DEFAULT-+-2))
 (11557 11557 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (9747 5085 (:REWRITE DEFAULT-+-1))
 (9719 35 (:REWRITE BVUMINUS-WHEN-BVCHOP-KNOWN-SUBST))
 (8013 189 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (5796 1538 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (5733 1812 (:REWRITE DEFAULT-<-1))
 (3814 1812 (:REWRITE DEFAULT-<-2))
 (3556 193 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (3528 300 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2723 317 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1615 966 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (1539 760 (:REWRITE DEFAULT-UNARY-MINUS))
 (1538 1538 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (1499 1499 (:REWRITE UBP-LONGER-BETTER))
 (1388 449 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1171 1171 (:REWRITE FOLD-CONSTS-IN-+))
 (1131 1131 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1021 82 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (483 1 (:REWRITE FROM-ONES-COMPLEMENT-OF-TO-ONES-COMPLEMENT))
 (456 300 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (456 300 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (456 300 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (456 300 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (456 1 (:DEFINITION REPRESENTABLE-AS-ONES-COMPLEMENTP))
 (402 402 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (402 402 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (346 38 (:REWRITE BVPLUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (309 309 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (309 309 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (253 253 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (208 35 (:REWRITE BVUMINUS-WHEN-ARG-IS-NOT-AN-INTEGER))
 (208 35 (:REWRITE BVMINUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (164 164 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (147 147 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (144 144 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (93 93 (:TYPE-PRESCRIPTION TO-ONES-COMPLEMENT))
 (59 59 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
 (59 59 (:REWRITE EQUAL-OF---AND-CONSTANT))
 (47 47 (:REWRITE EQUAL-OF-EXPT-AND-CONSTANT))
 (38 38 (:REWRITE BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (38 38 (:REWRITE BVPLUS-WHEN-NOT-NATP-ARG1-CHEAP))
 (38 38 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG3))
 (38 38 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG2))
 (38 38 (:REWRITE BVPLUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (38 38 (:REWRITE BVPLUS-SUBST-VALUE-ALT))
 (38 38 (:REWRITE BVPLUS-SUBST-VALUE))
 (35 35 (:REWRITE BVMINUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (35 35 (:REWRITE BVMINUS-WHEN-SIZE-IS-NOT-INTEGERP))
 (35 35 (:REWRITE BVMINUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (35 35 (:REWRITE BVMINUS-SUBST-VALUE-ARG-3))
 (35 35 (:REWRITE BVMINUS-SUBST-VALUE-ARG-2))
 (32 6 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (31 31 (:REWRITE UNSIGNED-BYTE-P-OF-TIMES-2))
 (25 5 (:REWRITE <-OF---AND--))
 (24 24 (:REWRITE DEFAULT-*-2))
 (24 24 (:REWRITE DEFAULT-*-1))
 (19 19 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (19 19 (:REWRITE BVCHOP-BOUND))
 (15 15 (:TYPE-PRESCRIPTION POSP))
 (8 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:TYPE-PRESCRIPTION REPRESENTABLE-AS-ONES-COMPLEMENTP))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 )
