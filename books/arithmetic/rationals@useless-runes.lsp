(DENOMINATOR-UNARY-MINUS
 (79 1 (:DEFINITION NONNEG-INT-GCD))
 (64 1 (:DEFINITION NONNEG-INT-MOD))
 (48 4 (:REWRITE NONNEG-INT-MOD-WHEN-DIVIDES))
 (24 1 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (21 3 (:REWRITE COMMUTATIVITY-OF-*))
 (18 1 (:REWRITE DISTRIBUTIVITY))
 (15 10 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (12 12 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (10 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 3 (:DEFINITION NFIX))
 (8 8 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-UNARY-/))
 (4 1 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE COMMUTATIVITY-OF-+))
 (1 1 (:REWRITE NONNEG-INT-MOD-+-0))
 (1 1 (:REWRITE INVERSE-OF-*))
 (1 1 (:REWRITE EQUAL-DENOMINATOR-1))
 )
(NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION
 (47 30 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (46 46 (:REWRITE DEFAULT-<-2))
 (46 46 (:REWRITE DEFAULT-<-1))
 (42 42 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (35 35 (:REWRITE DEFAULT-*-2))
 (35 35 (:REWRITE DEFAULT-*-1))
 (27 27 (:REWRITE DEFAULT-NUMERATOR))
 (22 2 (:LINEAR X*Y>1-POSITIVE))
 (20 2 (:REWRITE <-UNARY-/-POSITIVE-RIGHT))
 (15 15 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (6 6 (:REWRITE DEFAULT-DENOMINATOR))
 (4 2 (:REWRITE UNICITY-OF-1))
 (2 2 (:REWRITE EQUAL-DENOMINATOR-1))
 (2 2 (:LINEAR LEAST-NUMERATOR-DENOMINATOR-<= . 3))
 (2 2 (:LINEAR LEAST-NUMERATOR-DENOMINATOR-<= . 2))
 (2 2 (:DEFINITION FIX))
 )
(DENOMINATOR-PLUS
 (855 13 (:DEFINITION NONNEG-INT-MOD))
 (733 30 (:REWRITE NONNEG-INT-MOD-WHEN-DIVIDES))
 (167 18 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT))
 (166 166 (:REWRITE DEFAULT-*-2))
 (166 166 (:REWRITE DEFAULT-*-1))
 (142 62 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (111 111 (:REWRITE DEFAULT-<-2))
 (111 111 (:REWRITE DEFAULT-<-1))
 (81 81 (:REWRITE DEFAULT-+-2))
 (81 81 (:REWRITE DEFAULT-+-1))
 (70 70 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (63 31 (:REWRITE DEFAULT-UNARY-/))
 (61 3 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (59 59 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (59 59 (:REWRITE DEFAULT-DENOMINATOR))
 (45 45 (:REWRITE DEFAULT-UNARY-MINUS))
 (45 15 (:LINEAR X*Y>1-POSITIVE))
 (38 14 (:REWRITE NONNEG-INT-MOD-+-0))
 (34 34 (:REWRITE EQUAL-CONSTANT-+))
 (33 33 (:REWRITE DEFAULT-NUMERATOR))
 (30 8 (:REWRITE <-+-NEGATIVE-0-2))
 (24 8 (:REWRITE INVERSE-OF-+-AS=0))
 (24 8 (:REWRITE <-0-+-NEGATIVE-2))
 (21 21 (:REWRITE FOLD-CONSTS-IN-*))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (20 2 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (16 16 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (16 8 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
 (9 1 (:REWRITE <-*-0))
 (5 5 (:REWRITE EQUAL-DENOMINATOR-1))
 (3 1 (:REWRITE NONNEG-INT-GCD-ABS . 3))
 (3 1 (:REWRITE NONNEG-INT-GCD-ABS . 1))
 (3 1 (:REWRITE <-MINUS-ZERO))
 (3 1 (:DEFINITION IFF))
 )
(NUMERATOR-MINUS
 (79 1 (:DEFINITION NONNEG-INT-GCD))
 (64 1 (:DEFINITION NONNEG-INT-MOD))
 (48 4 (:REWRITE NONNEG-INT-MOD-WHEN-DIVIDES))
 (24 1 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (21 3 (:REWRITE COMMUTATIVITY-OF-*))
 (18 18 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (18 1 (:REWRITE DISTRIBUTIVITY))
 (17 12 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (14 14 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:REWRITE DEFAULT-*-2))
 (11 11 (:REWRITE DEFAULT-*-1))
 (10 1 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (9 9 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (9 9 (:REWRITE DEFAULT-DENOMINATOR))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 3 (:DEFINITION NFIX))
 (8 8 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (6 6 (:REWRITE DEFAULT-UNARY-/))
 (4 1 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE COMMUTATIVITY-OF-+))
 (1 1 (:REWRITE NONNEG-INT-MOD-+-0))
 (1 1 (:REWRITE INVERSE-OF-*))
 (1 1 (:REWRITE EQUAL-DENOMINATOR-1))
 )
(NUMERATOR-/X
 (96 1 (:DEFINITION NONNEG-INT-GCD))
 (78 1 (:DEFINITION NONNEG-INT-MOD))
 (60 2 (:REWRITE NONNEG-INT-MOD-WHEN-DIVIDES))
 (36 24 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (28 1 (:REWRITE DISTRIBUTIVITY))
 (23 22 (:REWRITE DEFAULT-<-1))
 (23 11 (:REWRITE DEFAULT-*-1))
 (22 22 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (16 11 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-UNARY-/))
 (11 3 (:REWRITE DEFAULT-+-1))
 (10 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 2 (:DEFINITION NFIX))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:REWRITE DEFAULT-NUMERATOR))
 (4 3 (:REWRITE DEFAULT-+-2))
 (4 1 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (4 1 (:REWRITE NONNEG-INT-MOD-+-0))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE INVERSE-OF-*))
 )
