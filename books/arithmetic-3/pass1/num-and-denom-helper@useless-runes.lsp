(NONNEG-INT-MOD
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(NONNEG-INT-MOD-<-DIVISOR
 (40 35 (:REWRITE DEFAULT-<-1))
 (35 35 (:REWRITE DEFAULT-<-2))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 4 (:REWRITE DEFAULT-+-2))
 (6 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(NONNEG-INT-MOD-NONNEGATIVE-INTEGER-QUOTIENT
 (105 99 (:REWRITE DEFAULT-<-1))
 (100 99 (:REWRITE DEFAULT-<-2))
 (60 44 (:REWRITE DEFAULT-+-2))
 (53 44 (:REWRITE DEFAULT-+-1))
 (21 13 (:REWRITE DEFAULT-*-2))
 (15 13 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(NONNEG-INT-MOD-0)
(INDUCT-ON-NONNEG-INT)
(HACK)
(NONNEG-INT-MOD-+-*
 (45 45 (:REWRITE DEFAULT-<-2))
 (45 45 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE DEFAULT-+-2))
 (27 27 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT))
 )
(NONNEG-INT-MOD-+-*-NONNEG-INT-MOD
 (136 136 (:REWRITE DEFAULT-<-2))
 (136 136 (:REWRITE DEFAULT-<-1))
 (71 71 (:REWRITE DEFAULT-+-2))
 (71 71 (:REWRITE DEFAULT-+-1))
 (34 34 (:REWRITE FOLD-CONSTS-IN-+))
 (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
 (15 15 (:REWRITE DEFAULT-*-2))
 (15 15 (:REWRITE DEFAULT-*-1))
 (6 2 (:REWRITE <-+-NEGATIVE-0-1))
 )
(NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1
 (162 147 (:REWRITE DEFAULT-<-1))
 (147 147 (:REWRITE DEFAULT-<-2))
 (99 91 (:REWRITE DEFAULT-+-2))
 (91 91 (:REWRITE DEFAULT-+-1))
 (65 5 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (43 43 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 22 (:REWRITE DEFAULT-*-2))
 (23 22 (:REWRITE DEFAULT-*-1))
 (19 19 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE FOLD-CONSTS-IN-*))
 (5 5 (:DEFINITION IFIX))
 )
(DIVISOR-NONNEGATIVE-INTEGER-QUOTIENT
 (52 51 (:REWRITE DEFAULT-<-2))
 (52 51 (:REWRITE DEFAULT-<-1))
 (26 20 (:REWRITE DEFAULT-+-2))
 (26 8 (:REWRITE COMMUTATIVITY-OF-+))
 (22 20 (:REWRITE DEFAULT-+-1))
 (18 8 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (10 6 (:REWRITE DEFAULT-*-2))
 (9 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 6 (:REWRITE DEFAULT-*-1))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE ZP-OPEN))
 )
(LEFT-NONNEG-INT-MOD-*
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:REWRITE DEFAULT-<-1))
 (14 3 (:REWRITE <-+-NEGATIVE-0-1))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (6 2 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (5 5 (:REWRITE ZP-OPEN))
 (5 2 (:REWRITE NONNEG-INT-MOD-+-*))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (3 1 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 (3 1 (:REWRITE <-MINUS-ZERO))
 (1 1 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(RIGHT-NONNEG-INT-MOD-*
 (3 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(NONNEG-INT-MOD-*-0
 (116 109 (:REWRITE DEFAULT-<-1))
 (113 109 (:REWRITE DEFAULT-<-2))
 (37 30 (:REWRITE DEFAULT-+-2))
 (35 28 (:REWRITE DEFAULT-*-2))
 (33 30 (:REWRITE DEFAULT-+-1))
 (32 28 (:REWRITE DEFAULT-*-1))
 (20 16 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (19 15 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (11 11 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE FOLD-CONSTS-IN-*))
 (4 4 (:DEFINITION IFIX))
 )
(NONNEG-INT-MOD-+-0
 (179 158 (:REWRITE DEFAULT-<-1))
 (158 158 (:REWRITE DEFAULT-<-2))
 (100 78 (:REWRITE DEFAULT-+-2))
 (86 78 (:REWRITE DEFAULT-+-1))
 (57 57 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (29 29 (:REWRITE DEFAULT-UNARY-MINUS))
 (22 6 (:REWRITE <-+-NEGATIVE-0-1))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-*))
 )
(NONNEG-INT-MOD-MINUS-0
 (246 198 (:REWRITE DEFAULT-<-1))
 (215 198 (:REWRITE DEFAULT-<-2))
 (128 103 (:REWRITE DEFAULT-+-2))
 (117 103 (:REWRITE DEFAULT-+-1))
 (88 33 (:REWRITE NONNEG-INT-MOD-+-0))
 (63 9 (:REWRITE <-*-LEFT-CANCEL))
 (59 46 (:REWRITE DEFAULT-UNARY-MINUS))
 (52 30 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (46 36 (:REWRITE DEFAULT-*-2))
 (40 36 (:REWRITE DEFAULT-*-1))
 (23 23 (:REWRITE ZP-OPEN))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 2 (:REWRITE NONNEG-INT-MOD-+-*))
 (16 4 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 )
(LINEAR-COMBINATION-NONNEG-INT-MOD
 (88 88 (:REWRITE DEFAULT-<-2))
 (88 88 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 20 (:REWRITE DEFAULT-*-2))
 (20 20 (:REWRITE DEFAULT-*-1))
 (20 2 (:REWRITE <-*-0))
 (18 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE ZP-OPEN))
 (3 3 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(DIVISOR-<=
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 )
(NONNEG-INT-MOD-1
 (17 1 (:DEFINITION NONNEG-INT-MOD))
 (6 2 (:DEFINITION NFIX))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NONNEG-INT-MOD-+-0))
 )
(NONNEG-INT-GCD
 (30 2 (:DEFINITION NONNEG-INT-MOD))
 (12 4 (:DEFINITION NFIX))
 (11 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-0))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE ZP-OPEN))
 )
(NONNEG-INT-GCD->-0
 (86 5 (:DEFINITION NONNEG-INT-MOD))
 (25 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE DEFAULT-<-1))
 (18 5 (:REWRITE COMMUTATIVITY-OF-+))
 (13 10 (:REWRITE DEFAULT-+-2))
 (13 10 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE NONNEG-INT-MOD-+-0))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE ZP-OPEN))
 )
(NONNEG-INT-GCD-IS-COMMON-DIVISOR
 (563 57 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (388 272 (:REWRITE DEFAULT-<-2))
 (298 272 (:REWRITE DEFAULT-<-1))
 (149 69 (:REWRITE DEFAULT-+-2))
 (143 63 (:REWRITE DEFAULT-UNARY-MINUS))
 (92 69 (:REWRITE DEFAULT-+-1))
 (28 4 (:REWRITE <-*-0))
 (25 25 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 3 (:REWRITE COMMUTATIVITY-OF-+))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (4 4 (:DEFINITION IFF))
 )
(NONNEG-INT-GCD-MULTIPLIER1
 (30 2 (:DEFINITION NONNEG-INT-MOD))
 (12 4 (:DEFINITION NFIX))
 (11 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-0))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE ZP-OPEN))
 )
(LINEAR-COMBINATION-FOR-NONNEG-INT-GCD
 (682 69 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (385 366 (:REWRITE DEFAULT-<-2))
 (373 366 (:REWRITE DEFAULT-<-1))
 (282 189 (:REWRITE DEFAULT-+-2))
 (238 189 (:REWRITE DEFAULT-+-1))
 (223 93 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (189 56 (:REWRITE ZP-OPEN))
 (176 100 (:REWRITE DEFAULT-*-2))
 (164 121 (:REWRITE DEFAULT-UNARY-MINUS))
 (149 100 (:REWRITE DEFAULT-*-1))
 (79 79 (:REWRITE NONNEG-INT-MOD-+-0))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE FOLD-CONSTS-IN-*))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 )
(NONNEG-INT-GCD-IS-LARGEST-COMMON-DIVISOR-MOD
 (147 130 (:REWRITE DEFAULT-<-1))
 (130 130 (:REWRITE DEFAULT-<-2))
 (60 46 (:REWRITE DEFAULT-+-2))
 (60 46 (:REWRITE DEFAULT-+-1))
 (41 18 (:REWRITE NONNEG-INT-MOD-+-0))
 (39 33 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (35 35 (:REWRITE ZP-OPEN))
 (33 6 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (32 22 (:REWRITE DEFAULT-*-1))
 (30 22 (:REWRITE DEFAULT-*-2))
 (25 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (19 1 (:REWRITE <-*-0))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (4 1 (:DEFINITION IFF))
 (2 1 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(NONNEG-INT-GCD-IS-LARGEST-COMMON-DIVISOR-<=
 (244 7 (:DEFINITION NONNEG-INT-MOD))
 (147 17 (:DEFINITION NFIX))
 (87 2 (:DEFINITION NONNEG-INT-GCD))
 (36 36 (:REWRITE DEFAULT-<-2))
 (36 36 (:REWRITE DEFAULT-<-1))
 (16 12 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (14 4 (:REWRITE COMMUTATIVITY-OF-+))
 (13 10 (:REWRITE DEFAULT-+-1))
 (12 10 (:REWRITE DEFAULT-+-2))
 (11 2 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (6 6 (:REWRITE NONNEG-INT-MOD-+-0))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:TYPE-PRESCRIPTION NFIX))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NONNEGATIVE-INTEGER-QUOTIENT-GCD
 (112 4 (:DEFINITION NONNEG-INT-GCD))
 (92 4 (:DEFINITION NONNEG-INT-MOD))
 (56 2 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (40 32 (:REWRITE DEFAULT-<-1))
 (40 4 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (36 36 (:TYPE-PRESCRIPTION NONNEG-INT-GCD->-0))
 (32 32 (:REWRITE DEFAULT-<-2))
 (20 4 (:REWRITE NONNEG-INT-GCD-IS-LARGEST-COMMON-DIVISOR-<=))
 (12 4 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (10 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 2 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NONNEG-INT-MOD-+-0))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:DEFINITION IFIX))
 )
(LINEAR-COMBINATION-GCD=1
 (317 57 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (292 275 (:REWRITE DEFAULT-<-2))
 (276 275 (:REWRITE DEFAULT-<-1))
 (255 169 (:REWRITE DEFAULT-+-2))
 (246 169 (:REWRITE DEFAULT-+-1))
 (233 125 (:REWRITE DEFAULT-*-2))
 (173 125 (:REWRITE DEFAULT-*-1))
 (156 37 (:REWRITE ZP-OPEN))
 (146 105 (:REWRITE DEFAULT-UNARY-MINUS))
 (104 52 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (66 66 (:REWRITE NONNEG-INT-MOD-+-0))
 (47 47 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (38 38 (:REWRITE FOLD-CONSTS-IN-*))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 )
(DIVISOR-OF-PRODUCT-DIVIDES-FACTOR
 (156 2 (:DEFINITION NONNEG-INT-GCD-MULTIPLIER2))
 (61 7 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (50 2 (:DEFINITION NONNEG-INT-GCD-MULTIPLIER1))
 (38 38 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE DEFAULT-<-1))
 (26 2 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (24 14 (:REWRITE DEFAULT-*-2))
 (23 23 (:TYPE-PRESCRIPTION NONNEG-INT-GCD->-0))
 (20 14 (:REWRITE DEFAULT-+-2))
 (20 8 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (19 14 (:REWRITE DEFAULT-*-1))
 (16 14 (:REWRITE DEFAULT-+-1))
 (16 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (10 2 (:REWRITE COMMUTATIVITY-OF-*))
 (7 7 (:REWRITE NONNEG-INT-MOD-+-0))
 (6 6 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE FOLD-CONSTS-IN-*))
 (2 2 (:REWRITE NONNEG-INT-MOD-*-0))
 (2 2 (:DEFINITION IFIX))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NONNEG-INT-MOD-ABS-+-*
 (631 62 (:REWRITE NONNEG-INT-MOD-+-0))
 (409 332 (:REWRITE DEFAULT-<-2))
 (388 9 (:REWRITE NONNEG-INT-MOD-*-0))
 (336 332 (:REWRITE DEFAULT-<-1))
 (187 29 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (182 132 (:REWRITE DEFAULT-+-2))
 (156 132 (:REWRITE DEFAULT-+-1))
 (128 31 (:REWRITE ZP-OPEN))
 (114 84 (:REWRITE DEFAULT-UNARY-MINUS))
 (42 42 (:REWRITE DEFAULT-*-2))
 (42 42 (:REWRITE DEFAULT-*-1))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (12 2 (:REWRITE ASSOCIATIVITY-OF-+))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 )
(NONNEG-INT-GCD-ABS->=
 (246 12 (:DEFINITION NONNEG-INT-MOD))
 (246 10 (:DEFINITION NONNEG-INT-GCD))
 (80 24 (:DEFINITION NFIX))
 (76 70 (:REWRITE DEFAULT-<-2))
 (72 70 (:REWRITE DEFAULT-<-1))
 (47 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (46 16 (:REWRITE NONNEG-INT-MOD-+-0))
 (44 12 (:REWRITE COMMUTATIVITY-OF-+))
 (38 34 (:REWRITE DEFAULT-+-2))
 (38 34 (:REWRITE DEFAULT-+-1))
 (27 3 (:REWRITE <-*-0))
 (25 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 6 (:REWRITE <-MINUS-ZERO))
 (22 4 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (12 4 (:REWRITE <-+-NEGATIVE-0-2))
 (12 4 (:DEFINITION IFF))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (9 1 (:REWRITE 0-<-*))
 (6 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (6 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 2 (:REWRITE NONNEG-INT-MOD-+-*))
 )
(NONNEG-INT-MOD-ABS
 (312 255 (:REWRITE DEFAULT-<-2))
 (256 255 (:REWRITE DEFAULT-<-1))
 (167 122 (:REWRITE DEFAULT-+-2))
 (135 90 (:REWRITE DEFAULT-UNARY-MINUS))
 (135 48 (:REWRITE NONNEG-INT-MOD-+-0))
 (129 122 (:REWRITE DEFAULT-+-1))
 (62 62 (:REWRITE DEFAULT-*-2))
 (62 62 (:REWRITE DEFAULT-*-1))
 (40 1 (:REWRITE NONNEG-INT-MOD-*-0))
 (12 4 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (12 4 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 4 (:REWRITE NONNEG-INT-MOD-+-*))
 (4 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-*))
 )
(NONNEG-INT-GCD-ABS-<=
 (246 10 (:DEFINITION NONNEG-INT-GCD))
 (244 12 (:DEFINITION NONNEG-INT-MOD))
 (80 24 (:DEFINITION NFIX))
 (76 70 (:REWRITE DEFAULT-<-2))
 (72 70 (:REWRITE DEFAULT-<-1))
 (46 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (42 16 (:REWRITE NONNEG-INT-MOD-+-0))
 (36 32 (:REWRITE DEFAULT-+-2))
 (34 10 (:REWRITE COMMUTATIVITY-OF-+))
 (34 6 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (32 32 (:REWRITE DEFAULT-+-1))
 (27 3 (:REWRITE <-*-0))
 (25 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 6 (:REWRITE <-MINUS-ZERO))
 (12 4 (:REWRITE <-+-NEGATIVE-0-2))
 (12 4 (:DEFINITION IFF))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (9 1 (:REWRITE 0-<-*))
 (6 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (6 2 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 2 (:REWRITE NONNEG-INT-MOD-+-*))
 )
(NONNEG-INT-GCD-ABS
 (984 45 (:DEFINITION NONNEG-INT-MOD))
 (450 5 (:REWRITE NONNEG-INT-GCD-IS-LARGEST-COMMON-DIVISOR-<=))
 (309 279 (:REWRITE DEFAULT-<-2))
 (289 279 (:REWRITE DEFAULT-<-1))
 (253 6 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (149 57 (:REWRITE NONNEG-INT-MOD-+-0))
 (137 117 (:REWRITE DEFAULT-+-2))
 (126 23 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (121 117 (:REWRITE DEFAULT-+-1))
 (119 28 (:REWRITE <-MINUS-ZERO))
 (96 76 (:REWRITE DEFAULT-UNARY-MINUS))
 (58 58 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (40 1 (:REWRITE NONNEG-INT-MOD-*-0))
 (36 12 (:REWRITE <-+-NEGATIVE-0-2))
 (33 33 (:REWRITE DEFAULT-*-2))
 (33 33 (:REWRITE DEFAULT-*-1))
 (18 6 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (18 6 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD))
 (14 6 (:REWRITE NONNEG-INT-MOD-+-*))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 )
(COMMUTATIVITY-OF-NONNEG-INT-GCD
 (30 30 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-<-1))
 (20 2 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (16 16 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (8 8 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 2 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (4 4 (:REWRITE NONNEG-INT-MOD-+-0))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CROSS-PRODUCT-FACTOR
 (200 200 (:TYPE-PRESCRIPTION NONNEG-INT-GCD->-0))
 (155 155 (:REWRITE DEFAULT-<-2))
 (155 155 (:REWRITE DEFAULT-<-1))
 (93 25 (:REWRITE NONNEG-INT-MOD-+-0))
 (90 12 (:REWRITE <-*-0))
 (63 21 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (60 10 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (49 49 (:REWRITE DEFAULT-+-2))
 (49 49 (:REWRITE DEFAULT-+-1))
 (43 14 (:REWRITE COMMUTATIVITY-OF-+))
 (29 1 (:REWRITE LINEAR-COMBINATION-NONNEG-INT-MOD))
 (28 28 (:REWRITE DEFAULT-*-2))
 (28 28 (:REWRITE DEFAULT-*-1))
 (26 26 (:REWRITE ZP-OPEN))
 (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:DEFINITION IFF))
 (3 3 (:REWRITE FOLD-CONSTS-IN-*))
 (3 1 (:REWRITE NONNEG-INT-MOD-+-*-NONNEG-INT-MOD-1))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(NONNEG-INT-GCD-1-RIGHT
 (1 1 (:REWRITE COMMUTATIVITY-OF-NONNEG-INT-GCD))
 )
(NONNEG-INT-GCD-1-LEFT
 (42 2 (:DEFINITION NONNEG-INT-MOD))
 (30 2 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (24 24 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (8 4 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(NONNEG-INT-GCD-NUMERATOR-DENOMINATOR
 (331 19 (:DEFINITION NONNEG-INT-MOD))
 (164 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (130 13 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (110 100 (:REWRITE DEFAULT-<-2))
 (108 108 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (108 100 (:REWRITE DEFAULT-<-1))
 (39 31 (:REWRITE DEFAULT-UNARY-MINUS))
 (39 13 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (35 23 (:REWRITE DEFAULT-+-2))
 (32 4 (:REWRITE NONNEG-INT-GCD-IS-LARGEST-COMMON-DIVISOR-<=))
 (23 23 (:REWRITE DEFAULT-+-1))
 (20 20 (:TYPE-PRESCRIPTION NFIX))
 (15 15 (:REWRITE NONNEG-INT-MOD-+-0))
 (5 3 (:REWRITE DEFAULT-*-2))
 (4 4 (:DEFINITION IFIX))
 (3 3 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE FOLD-CONSTS-IN-*))
 )
(LOWEST-TERMS-NONNEG-INT-MOD
 (107 107 (:REWRITE DEFAULT-<-2))
 (107 107 (:REWRITE DEFAULT-<-1))
 (86 4 (:DEFINITION NONNEG-INT-GCD))
 (42 42 (:REWRITE DEFAULT-*-2))
 (42 42 (:REWRITE DEFAULT-*-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 25 (:REWRITE DEFAULT-+-2))
 (25 25 (:REWRITE DEFAULT-+-1))
 (22 4 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (20 20 (:REWRITE FOLD-CONSTS-IN-*))
 (20 1 (:REWRITE 0-<-*))
 (16 16 (:REWRITE DEFAULT-UNARY-/))
 (15 15 (:REWRITE NONNEG-INT-MOD-+-0))
 (8 5 (:REWRITE ZP-OPEN))
 )
(LOWEST-TERMS-<=
 (86 86 (:REWRITE DEFAULT-<-2))
 (86 86 (:REWRITE DEFAULT-<-1))
 (43 2 (:DEFINITION NONNEG-INT-GCD))
 (20 1 (:REWRITE 0-<-*))
 (18 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 (18 6 (:REWRITE COMMUTATIVITY-OF-+))
 (15 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE DEFAULT-UNARY-/))
 (10 1 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (9 9 (:REWRITE NONNEG-INT-MOD-+-0))
 (6 6 (:REWRITE FOLD-CONSTS-IN-*))
 (5 2 (:REWRITE ZP-OPEN))
 )
(LEAST-NUMERATOR-DENOMINATOR-NONNEG-INT-MOD
 (93 93 (:REWRITE DEFAULT-<-2))
 (93 93 (:REWRITE DEFAULT-<-1))
 (93 12 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (34 34 (:REWRITE DEFAULT-UNARY-/))
 (34 34 (:REWRITE DEFAULT-*-2))
 (34 34 (:REWRITE DEFAULT-*-1))
 (31 1 (:DEFINITION NONNEG-INT-GCD))
 (25 25 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE NONNEG-INT-MOD-+-0))
 (13 13 (:REWRITE DEFAULT-DENOMINATOR))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (3 1 (:REWRITE <-0-MINUS))
 )
(LEAST-NUMERATOR-DENOMINATOR-<=
 (45 45 (:REWRITE DEFAULT-<-2))
 (45 45 (:REWRITE DEFAULT-<-1))
 (20 2 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (13 13 (:REWRITE DEFAULT-UNARY-/))
 (13 13 (:REWRITE DEFAULT-*-2))
 (13 13 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (6 2 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-0))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(UNIQUE-RATIONALP
 (43 2 (:DEFINITION NONNEG-INT-GCD))
 (37 2 (:DEFINITION NONNEG-INT-MOD))
 (21 21 (:REWRITE DEFAULT-UNARY-/))
 (21 21 (:REWRITE DEFAULT-*-2))
 (21 21 (:REWRITE DEFAULT-*-1))
 (19 19 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE DEFAULT-<-1))
 (15 5 (:DEFINITION NFIX))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (10 1 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (9 9 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (2 2 (:REWRITE NONNEG-INT-MOD-+-0))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:DEFINITION FIX))
 )
