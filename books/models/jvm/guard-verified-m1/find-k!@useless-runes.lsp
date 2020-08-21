(M1::FAST-LESSP-LOOP-CLOCK (8 8 (:TYPE-PRESCRIPTION MIN)))
(M1::LESSP-LOOP-CLOCK-LEMMA
     (48 43 (:REWRITE DEFAULT-PLUS-2))
     (46 41 (:REWRITE DEFAULT-LESS-THAN-1))
     (44 39
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (44 39 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (43 43 (:REWRITE DEFAULT-PLUS-1))
     (41 41 (:REWRITE THE-FLOOR-BELOW))
     (41 41 (:REWRITE THE-FLOOR-ABOVE))
     (41 41
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (41 41
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (41 41
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (41 41
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (41 41 (:REWRITE INTEGERP-<-CONSTANT))
     (41 41 (:REWRITE DEFAULT-LESS-THAN-2))
     (41 41 (:REWRITE CONSTANT-<-INTEGERP))
     (41 41
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (41 41
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (41 41
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (41 41
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (41 41 (:REWRITE |(< c (- x))|))
     (41 41
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (41 41
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (41 41
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (41 41
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (41 41 (:REWRITE |(< (/ x) (/ y))|))
     (41 41 (:REWRITE |(< (- x) c)|))
     (41 41 (:REWRITE |(< (- x) (- y))|))
     (39 39 (:REWRITE SIMPLIFY-SUMS-<))
     (37 37
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (37 37 (:REWRITE NORMALIZE-ADDENDS))
     (29 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (29 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (29 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (23 23 (:REWRITE |(< (/ x) 0)|))
     (23 23 (:REWRITE |(< (* x y) 0)|))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:REWRITE DEFAULT-TIMES-2))
     (14 14 (:REWRITE DEFAULT-TIMES-1))
     (14 14 (:META META-INTEGERP-CORRECT))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(M1::FAST-LESSP-CLOCK (12 12 (:TYPE-PRESCRIPTION MIN)))
(M1::FAST-LESSP-CLOCK-LEMMA
     (12477 894
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12474 1782 (:REWRITE ACL2-NUMBERP-X))
     (3564 891 (:REWRITE RATIONALP-X))
     (3564 891
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1785 894
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1784 1784 (:REWRITE REDUCE-INTEGERP-+))
     (1784 1784 (:REWRITE INTEGERP-MINUS-X))
     (1784 1784 (:META META-INTEGERP-CORRECT))
     (894 894 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (894 894
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (894 894
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (894 894
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (894 894 (:REWRITE |(equal c (/ x))|))
     (894 894 (:REWRITE |(equal c (- x))|))
     (894 894 (:REWRITE |(equal (/ x) c)|))
     (894 894 (:REWRITE |(equal (/ x) (/ y))|))
     (894 894 (:REWRITE |(equal (- x) c)|))
     (894 894 (:REWRITE |(equal (- x) (- y))|))
     (891 891 (:REWRITE REDUCE-RATIONALP-+))
     (891 891 (:REWRITE REDUCE-RATIONALP-*))
     (891 891 (:REWRITE RATIONALP-MINUS-X))
     (891 891 (:META META-RATIONALP-CORRECT))
     (265 74 (:REWRITE DEFAULT-PLUS-2))
     (89 74 (:REWRITE DEFAULT-PLUS-1))
     (49 22 (:REWRITE DEFAULT-LESS-THAN-1))
     (43 19 (:REWRITE DEFAULT-TIMES-2))
     (42 20
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (35 35
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (25 22 (:REWRITE DEFAULT-LESS-THAN-2))
     (23 20 (:REWRITE |(< (- x) c)|))
     (23 20 (:REWRITE |(< (- x) (- y))|))
     (22 22 (:REWRITE THE-FLOOR-BELOW))
     (22 22 (:REWRITE THE-FLOOR-ABOVE))
     (21 21 (:REWRITE DEFAULT-CDR))
     (21 3 (:DEFINITION LEN))
     (20 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 20
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (20 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (20 20 (:REWRITE INTEGERP-<-CONSTANT))
     (20 20 (:REWRITE CONSTANT-<-INTEGERP))
     (20 20
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (20 20
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (20 20
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (20 20
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (20 20 (:REWRITE |(< c (- x))|))
     (20 20
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (20 20
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (20 20
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (20 20
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (20 20 (:REWRITE |(< (/ x) (/ y))|))
     (19 19 (:REWRITE DEFAULT-TIMES-1))
     (17 17 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE FOLD-CONSTS-IN-+))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 6 (:REWRITE DEFAULT-MINUS))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (+ (- c) x) y)|))
     (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE |(* (- x) y)|)))
(M1::FAST-MOD-LOOP-CLOCK (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                         (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                         (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                         (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                         (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                         (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                         (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                         (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                         (25 5
                             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                         (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                         (1 1 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                         (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                         (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                         (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                         (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                         (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                         (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                         (1 1 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                         (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                         (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                         (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                         (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-1)))
(M1::FAST-MOD-LOOP-CLOCK-LEMMA
     (35068 1548 (:REWRITE DEFAULT-PLUS-2))
     (23909 23909
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (23909 23909
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (14642 1548 (:REWRITE DEFAULT-PLUS-1))
     (13750 1110
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (10933 1245
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (9718 1110
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (6225 1245
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (6225 1245
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (6225 1245
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (6225 1245
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (5550 1110
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (5550 1110
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (5550 1110
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (4323 716 (:REWRITE DEFAULT-TIMES-2))
     (3471 50
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3160 632 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3044 632 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2896 632
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2896 632
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2302 286
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2004 632 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1248 716 (:REWRITE DEFAULT-TIMES-1))
     (755 151
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (664 9 (:REWRITE FLOOR-ZERO . 3))
     (656 332 (:REWRITE DEFAULT-LESS-THAN-1))
     (646 102
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (632 632 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (632 632
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (632 632
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (632 632
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (632 632 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (603 603
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (491 21 (:REWRITE MOD-ZERO . 3))
     (455 21 (:REWRITE MOD-X-Y-=-X . 4))
     (398 398
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (391 21 (:REWRITE FLOOR-=-X/Y . 3))
     (391 21 (:REWRITE FLOOR-=-X/Y . 2))
     (384 320
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (366 16 (:REWRITE FLOOR-ZERO . 5))
     (334 30 (:REWRITE DEFAULT-MOD-RATIO))
     (332 332 (:REWRITE THE-FLOOR-BELOW))
     (332 332 (:REWRITE THE-FLOOR-ABOVE))
     (332 332 (:REWRITE DEFAULT-LESS-THAN-2))
     (330 330
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (330 330
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (320 320 (:REWRITE INTEGERP-<-CONSTANT))
     (320 320 (:REWRITE CONSTANT-<-INTEGERP))
     (320 320
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (320 320
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (320 320
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (320 320
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (320 320 (:REWRITE |(< c (- x))|))
     (320 320
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (320 320
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (320 320
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (320 320
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (320 320 (:REWRITE |(< (/ x) (/ y))|))
     (320 320 (:REWRITE |(< (- x) c)|))
     (320 320 (:REWRITE |(< (- x) (- y))|))
     (271 21 (:REWRITE MOD-ZERO . 4))
     (248 96 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (244 21 (:REWRITE DEFAULT-FLOOR-RATIO))
     (201 201 (:REWRITE FOLD-CONSTS-IN-+))
     (183 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (183 21 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (180 180
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (180 180 (:REWRITE DEFAULT-DIVIDE))
     (150 30 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (145 57 (:REWRITE DEFAULT-MINUS))
     (126 6 (:LINEAR MOD-BOUNDS-3))
     (120 120 (:REWRITE INTEGERP-MINUS-X))
     (119 119 (:META META-INTEGERP-CORRECT))
     (112 112 (:REWRITE |(< (+ c/d x) y)|))
     (109 109 (:REWRITE |(< (+ (- c) x) y)|))
     (108 108 (:REWRITE |(< (* x y) 0)|))
     (106 106 (:REWRITE |(< (/ x) 0)|))
     (105 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (105 21 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (105 21 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (91 91
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (91 91
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (70 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (65 13 (:REWRITE MOD-X-Y-=-X . 2))
     (65 13 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (65 13
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (60 12
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (60 12 (:REWRITE MOD-CANCEL-*-CONST))
     (60 12
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (60 12
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (60 12 (:LINEAR MOD-BOUNDS-2))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (50 50 (:REWRITE |(equal c (/ x))|))
     (50 50 (:REWRITE |(equal c (- x))|))
     (50 50 (:REWRITE |(equal (/ x) c)|))
     (50 50 (:REWRITE |(equal (/ x) (/ y))|))
     (50 50 (:REWRITE |(equal (- x) c)|))
     (50 50 (:REWRITE |(equal (- x) (- y))|))
     (50 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (45 9 (:REWRITE FLOOR-ZERO . 2))
     (42 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (40 8
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (40 8
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (40 8
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (36 36 (:REWRITE |(< 0 (* x y))|))
     (32 8 (:REWRITE FLOOR-CANCEL-*-CONST))
     (31 31 (:REWRITE |(equal (+ (- c) x) y)|))
     (31 31 (:REWRITE |(< 0 (/ x))|))
     (30 30 (:REWRITE DEFAULT-MOD-2))
     (30 30 (:REWRITE DEFAULT-MOD-1))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (21 21 (:REWRITE DEFAULT-FLOOR-2))
     (21 21 (:REWRITE DEFAULT-FLOOR-1))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14 (:REWRITE |(* c (* d x))|))
     (12 12
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (12 12 (:REWRITE |(mod x (- y))| . 3))
     (12 12 (:REWRITE |(mod x (- y))| . 2))
     (12 12 (:REWRITE |(mod x (- y))| . 1))
     (12 12
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (12 12 (:REWRITE |(mod (- x) y)| . 3))
     (12 12 (:REWRITE |(mod (- x) y)| . 2))
     (12 12 (:REWRITE |(mod (- x) y)| . 1))
     (12 12
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (8 8
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (8 8 (:REWRITE |(floor x (- y))| . 2))
     (8 8 (:REWRITE |(floor x (- y))| . 1))
     (8 8
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (8 8 (:REWRITE |(floor (- x) y)| . 2))
     (8 8 (:REWRITE |(floor (- x) y)| . 1))
     (8 8
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (8 8
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (5 5
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (5 5
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (5 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(floor (+ x r) i)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|)))
(M1::NATP-FAST-MOD-LOOP-CLOCK-LEMMA
     (3463 99 (:REWRITE DEFAULT-PLUS-2))
     (2879 99 (:REWRITE DEFAULT-PLUS-1))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (891 99
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (768 25 (:REWRITE DEFAULT-TIMES-2))
     (650 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (495 99 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (495 99
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (495 99
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (495 99
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (450 50
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (450 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (315 63 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (315 63 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (315 63
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (315 63
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (250 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (103 63 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (75 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (75 15 (:REWRITE DEFAULT-LESS-THAN-1))
     (71 15 (:REWRITE SIMPLIFY-SUMS-<))
     (69 1 (:REWRITE FLOOR-ZERO . 3))
     (63 63 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (63 63
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (63 63 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (63 63
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (63 63 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (48 48 (:REWRITE NORMALIZE-ADDENDS))
     (47 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (39 1 (:REWRITE CANCEL-MOD-+))
     (39 1 (:REWRITE CANCEL-FLOOR-+))
     (35 1 (:REWRITE MOD-X-Y-=-X . 4))
     (35 1 (:REWRITE FLOOR-ZERO . 5))
     (32 2 (:REWRITE |(integerp (- x))|))
     (31 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (31 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (30 1 (:REWRITE MOD-X-Y-=-X . 3))
     (30 1 (:REWRITE FLOOR-ZERO . 4))
     (25 25 (:REWRITE DEFAULT-TIMES-1))
     (21 1 (:REWRITE MOD-ZERO . 3))
     (21 1 (:REWRITE FLOOR-=-X/Y . 3))
     (21 1 (:REWRITE FLOOR-=-X/Y . 2))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 2 (:REWRITE |(* (- x) y)|))
     (18 1 (:REWRITE MOD-ZERO . 4))
     (15 15 (:REWRITE THE-FLOOR-BELOW))
     (15 15 (:REWRITE THE-FLOOR-ABOVE))
     (15 15
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15 (:REWRITE INTEGERP-<-CONSTANT))
     (15 15 (:REWRITE DEFAULT-LESS-THAN-2))
     (15 15 (:REWRITE CONSTANT-<-INTEGERP))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< c (- x))|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 15 (:REWRITE |(< (- x) c)|))
     (15 15 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (10 2 (:REWRITE DEFAULT-MINUS))
     (10 1 (:REWRITE DEFAULT-MOD-RATIO))
     (10 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (8 8 (:REWRITE DEFAULT-DIVIDE))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (5 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (5 1 (:REWRITE MOD-X-Y-=-X . 2))
     (5 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE MOD-CANCEL-*-CONST))
     (5 1 (:REWRITE FLOOR-ZERO . 2))
     (5 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (5 1
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (5 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (5 1
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (5 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (5 1
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (5 1
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-MOD-LOOP-CLOCK-LEMMA))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE |(* c (* d x))|))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor x (- y))| . 2))
     (1 1 (:REWRITE |(floor x (- y))| . 1))
     (1 1
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor (- x) y)| . 2))
     (1 1 (:REWRITE |(floor (- x) y)| . 1))
     (1 1
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(M1::FAST-MOD-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-MOD-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-MOD-CLOCK-LEMMA
     (19415 1397
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (19404 2772 (:REWRITE ACL2-NUMBERP-X))
     (5544 1386 (:REWRITE RATIONALP-X))
     (5544 1386
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (2783 1397
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2774 2774 (:REWRITE REDUCE-INTEGERP-+))
     (2774 2774 (:REWRITE INTEGERP-MINUS-X))
     (2774 2774 (:META META-INTEGERP-CORRECT))
     (1397 1397 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1397 1397
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1397 1397
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1397 1397
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1397 1397 (:REWRITE |(equal c (/ x))|))
     (1397 1397 (:REWRITE |(equal c (- x))|))
     (1397 1397 (:REWRITE |(equal (/ x) c)|))
     (1397 1397 (:REWRITE |(equal (/ x) (/ y))|))
     (1397 1397 (:REWRITE |(equal (- x) c)|))
     (1397 1397 (:REWRITE |(equal (- x) (- y))|))
     (1386 1386 (:REWRITE REDUCE-RATIONALP-+))
     (1386 1386 (:REWRITE REDUCE-RATIONALP-*))
     (1386 1386 (:REWRITE RATIONALP-MINUS-X))
     (1386 1386 (:META META-RATIONALP-CORRECT))
     (104 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (30 30 (:REWRITE DEFAULT-CDR))
     (28 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (26 26
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (26 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(M1::NATP-FAST-MOD-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-MOD-CLOCK-LEMMA)))
(M1::FAST-FLOOR-LOOP-CLOCK (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                           (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                           (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                           (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                           (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                           (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                           (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                           (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                           (25 5
                               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                           (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                           (1 1 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                           (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                           (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                           (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                           (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                           (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                           (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                           (1 1 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                           (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                           (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                           (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                           (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-1)))
(M1::FAST-FLOOR-LOOP-CLOCK-LEMMA
     (34939 1571 (:REWRITE DEFAULT-PLUS-2))
     (25057 25057
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (25057 25057
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (14663 1571 (:REWRITE DEFAULT-PLUS-1))
     (14296 1152
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (11455 1303
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (10096 1152
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (6515 1303
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (6515 1303
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (6515 1303
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (6515 1303
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (5760 1152
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (5760 1152
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (5760 1152
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (4323 716 (:REWRITE DEFAULT-TIMES-2))
     (3480 696 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3471 50
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3364 696 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3216 696
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (3216 696
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2446 302
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2196 696 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1248 716 (:REWRITE DEFAULT-TIMES-1))
     (755 151
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (696 696 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (696 696
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (696 696
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (696 696
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (696 696 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (670 346 (:REWRITE DEFAULT-LESS-THAN-1))
     (664 9 (:REWRITE FLOOR-ZERO . 3))
     (646 102
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (615 615
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (491 21 (:REWRITE MOD-ZERO . 3))
     (455 21 (:REWRITE MOD-X-Y-=-X . 4))
     (398 398
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (398 334
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (391 21 (:REWRITE FLOOR-=-X/Y . 3))
     (391 21 (:REWRITE FLOOR-=-X/Y . 2))
     (366 16 (:REWRITE FLOOR-ZERO . 5))
     (346 346 (:REWRITE THE-FLOOR-BELOW))
     (346 346 (:REWRITE THE-FLOOR-ABOVE))
     (346 346 (:REWRITE DEFAULT-LESS-THAN-2))
     (344 344
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (344 344
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (334 334 (:REWRITE INTEGERP-<-CONSTANT))
     (334 334 (:REWRITE CONSTANT-<-INTEGERP))
     (334 334
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (334 334
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (334 334
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (334 334
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (334 334 (:REWRITE |(< c (- x))|))
     (334 334
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (334 334
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (334 334
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (334 334
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (334 334 (:REWRITE |(< (/ x) (/ y))|))
     (334 334 (:REWRITE |(< (- x) c)|))
     (334 334 (:REWRITE |(< (- x) (- y))|))
     (334 30 (:REWRITE DEFAULT-MOD-RATIO))
     (271 21 (:REWRITE MOD-ZERO . 4))
     (248 96 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (244 21 (:REWRITE DEFAULT-FLOOR-RATIO))
     (201 201 (:REWRITE FOLD-CONSTS-IN-+))
     (183 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (183 21 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (180 180
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (180 180 (:REWRITE DEFAULT-DIVIDE))
     (150 30 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (145 57 (:REWRITE DEFAULT-MINUS))
     (134 134 (:REWRITE INTEGERP-MINUS-X))
     (133 133 (:META META-INTEGERP-CORRECT))
     (126 6 (:LINEAR MOD-BOUNDS-3))
     (122 122 (:REWRITE |(< (* x y) 0)|))
     (120 120 (:REWRITE |(< (/ x) 0)|))
     (112 112 (:REWRITE |(< (+ c/d x) y)|))
     (109 109 (:REWRITE |(< (+ (- c) x) y)|))
     (105 105
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (105 105
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (105 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (105 21 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (105 21 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (70 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (65 13 (:REWRITE MOD-X-Y-=-X . 2))
     (65 13 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (65 13
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (60 12
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (60 12 (:REWRITE MOD-CANCEL-*-CONST))
     (60 12
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (60 12
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (60 12 (:LINEAR MOD-BOUNDS-2))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (50 50 (:REWRITE |(equal c (/ x))|))
     (50 50 (:REWRITE |(equal c (- x))|))
     (50 50 (:REWRITE |(equal (/ x) c)|))
     (50 50 (:REWRITE |(equal (/ x) (/ y))|))
     (50 50 (:REWRITE |(equal (- x) c)|))
     (50 50 (:REWRITE |(equal (- x) (- y))|))
     (50 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (45 9 (:REWRITE FLOOR-ZERO . 2))
     (42 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (40 8
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (40 8
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (40 8
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (36 36 (:REWRITE |(< 0 (* x y))|))
     (32 8 (:REWRITE FLOOR-CANCEL-*-CONST))
     (31 31 (:REWRITE |(equal (+ (- c) x) y)|))
     (31 31 (:REWRITE |(< 0 (/ x))|))
     (30 30 (:REWRITE DEFAULT-MOD-2))
     (30 30 (:REWRITE DEFAULT-MOD-1))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (21 21 (:REWRITE DEFAULT-FLOOR-2))
     (21 21 (:REWRITE DEFAULT-FLOOR-1))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14 (:REWRITE |(* c (* d x))|))
     (12 12
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (12 12 (:REWRITE |(mod x (- y))| . 3))
     (12 12 (:REWRITE |(mod x (- y))| . 2))
     (12 12 (:REWRITE |(mod x (- y))| . 1))
     (12 12
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (12 12 (:REWRITE |(mod (- x) y)| . 3))
     (12 12 (:REWRITE |(mod (- x) y)| . 2))
     (12 12 (:REWRITE |(mod (- x) y)| . 1))
     (12 12
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (8 8
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (8 8 (:REWRITE |(floor x (- y))| . 2))
     (8 8 (:REWRITE |(floor x (- y))| . 1))
     (8 8
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (8 8 (:REWRITE |(floor (- x) y)| . 2))
     (8 8 (:REWRITE |(floor (- x) y)| . 1))
     (8 8
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (8 8
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (5 5
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (5 5
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (5 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(floor (+ x r) i)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|)))
(M1::NATP-FAST-FLOOR-LOOP-CLOCK-LEMMA
     (3463 99 (:REWRITE DEFAULT-PLUS-2))
     (2879 99 (:REWRITE DEFAULT-PLUS-1))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1613 1613
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (891 99
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (768 25 (:REWRITE DEFAULT-TIMES-2))
     (650 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (495 99 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (495 99
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (495 99
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (495 99
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (450 50
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (450 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (315 63 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (315 63 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (315 63
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (315 63
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (250 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (103 63 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (76 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (76 16 (:REWRITE DEFAULT-LESS-THAN-1))
     (72 16 (:REWRITE SIMPLIFY-SUMS-<))
     (69 1 (:REWRITE FLOOR-ZERO . 3))
     (63 63 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (63 63
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (63 63 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (63 63
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (63 63 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (48 48 (:REWRITE NORMALIZE-ADDENDS))
     (48 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (39 1 (:REWRITE CANCEL-MOD-+))
     (39 1 (:REWRITE CANCEL-FLOOR-+))
     (35 1 (:REWRITE MOD-X-Y-=-X . 4))
     (35 1 (:REWRITE FLOOR-ZERO . 5))
     (32 2 (:REWRITE |(integerp (- x))|))
     (31 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (31 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (30 1 (:REWRITE MOD-X-Y-=-X . 3))
     (30 1 (:REWRITE FLOOR-ZERO . 4))
     (25 25 (:REWRITE DEFAULT-TIMES-1))
     (21 1 (:REWRITE MOD-ZERO . 3))
     (21 1 (:REWRITE FLOOR-=-X/Y . 3))
     (21 1 (:REWRITE FLOOR-=-X/Y . 2))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 2 (:REWRITE |(* (- x) y)|))
     (18 1 (:REWRITE MOD-ZERO . 4))
     (16 16 (:REWRITE THE-FLOOR-BELOW))
     (16 16 (:REWRITE THE-FLOOR-ABOVE))
     (16 16
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (16 16
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (16 16
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (16 16 (:REWRITE INTEGERP-<-CONSTANT))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 16 (:REWRITE CONSTANT-<-INTEGERP))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< c (- x))|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< (/ x) (/ y))|))
     (16 16 (:REWRITE |(< (- x) c)|))
     (16 16 (:REWRITE |(< (- x) (- y))|))
     (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (10 2 (:REWRITE DEFAULT-MINUS))
     (10 1 (:REWRITE DEFAULT-MOD-RATIO))
     (10 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE DEFAULT-DIVIDE))
     (8 8 (:META META-INTEGERP-CORRECT))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (5 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (5 1 (:REWRITE MOD-X-Y-=-X . 2))
     (5 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE MOD-CANCEL-*-CONST))
     (5 1 (:REWRITE FLOOR-ZERO . 2))
     (5 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (5 1
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (5 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (5 1
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (5 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (5 1
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (5 1
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-FLOOR-LOOP-CLOCK-LEMMA))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE |(* c (* d x))|))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor x (- y))| . 2))
     (1 1 (:REWRITE |(floor x (- y))| . 1))
     (1 1
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor (- x) y)| . 2))
     (1 1 (:REWRITE |(floor (- x) y)| . 1))
     (1 1
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(M1::FAST-FLOOR-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-FLOOR-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-FLOOR-CLOCK-LEMMA
     (19415 1397
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (19404 2772 (:REWRITE ACL2-NUMBERP-X))
     (5544 1386 (:REWRITE RATIONALP-X))
     (5544 1386
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (2783 1397
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2775 2775 (:REWRITE REDUCE-INTEGERP-+))
     (2775 2775 (:REWRITE INTEGERP-MINUS-X))
     (2775 2775 (:META META-INTEGERP-CORRECT))
     (1397 1397 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1397 1397
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1397 1397
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1397 1397
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1397 1397 (:REWRITE |(equal c (/ x))|))
     (1397 1397 (:REWRITE |(equal c (- x))|))
     (1397 1397 (:REWRITE |(equal (/ x) c)|))
     (1397 1397 (:REWRITE |(equal (/ x) (/ y))|))
     (1397 1397 (:REWRITE |(equal (- x) c)|))
     (1397 1397 (:REWRITE |(equal (- x) (- y))|))
     (1386 1386 (:REWRITE REDUCE-RATIONALP-+))
     (1386 1386 (:REWRITE REDUCE-RATIONALP-*))
     (1386 1386 (:REWRITE RATIONALP-MINUS-X))
     (1386 1386 (:META META-RATIONALP-CORRECT))
     (104 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (30 30
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (30 30 (:REWRITE DEFAULT-CDR))
     (29 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (27 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (13 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 11 (:REWRITE |(< (- x) c)|))
     (13 11 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (11 11 (:REWRITE INTEGERP-<-CONSTANT))
     (11 11 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< c (- x))|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(M1::NATP-FAST-FLOOR-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-FLOOR-CLOCK-LEMMA)))
(M1::FAST-LOG2-LOOP-CLOCK
     (81 31 (:REWRITE DEFAULT-PLUS-2))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (76 23 (:REWRITE DEFAULT-LESS-THAN-1))
     (75 31 (:REWRITE DEFAULT-PLUS-1))
     (67 67 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (28 23 (:REWRITE DEFAULT-LESS-THAN-2))
     (23 23 (:REWRITE THE-FLOOR-BELOW))
     (23 23 (:REWRITE THE-FLOOR-ABOVE))
     (22 22 (:REWRITE DEFAULT-TIMES-2))
     (22 22 (:REWRITE DEFAULT-TIMES-1))
     (20 17
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 15 (:REWRITE |(< (- x) (- y))|))
     (19 6 (:REWRITE DEFAULT-MINUS))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< c (- x))|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (13 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (9 1
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (9 1
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (9 1
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (+ (- c) x) y)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:REWRITE |(* (- x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE |(< (/ x) y) with (< x 0)|)))
(M1::FAST-LOG2-LOOP-CLOCK-LEMMA
     (624 243 (:REWRITE DEFAULT-PLUS-2))
     (401 24 (:REWRITE DEFAULT-FLOOR-RATIO))
     (315 21 (:REWRITE |(* x (+ y z))|))
     (293 243 (:REWRITE DEFAULT-PLUS-1))
     (222 6 (:REWRITE ZP-OPEN))
     (211 211 (:REWRITE DEFAULT-TIMES-2))
     (211 211 (:REWRITE DEFAULT-TIMES-1))
     (209 209
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (209 209
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (209 209
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (209 209
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (207 1 (:REWRITE |(floor (if a b c) x)|))
     (190 25 (:REWRITE |(* y x)|))
     (168 42 (:REWRITE |(* c (* d x))|))
     (158 158
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (158 158 (:REWRITE NORMALIZE-ADDENDS))
     (124 124
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (100 58 (:REWRITE DEFAULT-LESS-THAN-1))
     (97 55
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (97 55 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (94 44 (:REWRITE REDUCE-INTEGERP-+))
     (78 6 (:REWRITE |(* (* x y) z)|))
     (77 1 (:REWRITE |(< (if a b c) x)|))
     (70 1 (:REWRITE |(< x (if a b c))|))
     (64 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (64 45
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (64 45
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (58 58 (:REWRITE THE-FLOOR-BELOW))
     (58 58 (:REWRITE THE-FLOOR-ABOVE))
     (58 58 (:REWRITE DEFAULT-LESS-THAN-2))
     (57 56
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (57 56
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (57 1 (:REWRITE |(equal (if a b c) x)|))
     (56 56
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (56 56
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (56 56 (:REWRITE INTEGERP-<-CONSTANT))
     (56 56 (:REWRITE CONSTANT-<-INTEGERP))
     (56 56
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (56 56
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (56 56
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (56 56
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (56 56 (:REWRITE |(< c (- x))|))
     (56 56
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (56 56
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (56 56
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (56 56
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (56 56 (:REWRITE |(< (/ x) (/ y))|))
     (56 56 (:REWRITE |(< (- x) c)|))
     (56 56 (:REWRITE |(< (- x) (- y))|))
     (56 52
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (55 55 (:REWRITE SIMPLIFY-SUMS-<))
     (53 53 (:TYPE-PRESCRIPTION NATP))
     (52 4
         (:REWRITE |(not (equal (* (/ x) y) 1))|))
     (52 4 (:REWRITE |(equal (* (/ x) y) 1)|))
     (51 51 (:REWRITE |(< (/ x) 0)|))
     (51 51 (:REWRITE |(< (* x y) 0)|))
     (50 50
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (50 50
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (45 45
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (45 45 (:REWRITE |(equal c (/ x))|))
     (45 45 (:REWRITE |(equal c (- x))|))
     (45 45 (:REWRITE |(equal (/ x) c)|))
     (45 45 (:REWRITE |(equal (/ x) (/ y))|))
     (45 45 (:REWRITE |(equal (- x) c)|))
     (45 45 (:REWRITE |(equal (- x) (- y))|))
     (44 44 (:REWRITE INTEGERP-MINUS-X))
     (44 44 (:META META-INTEGERP-CORRECT))
     (42 42 (:REWRITE FOLD-CONSTS-IN-+))
     (41 1 (:REWRITE |(* (if a b c) x)|))
     (28 1 (:REWRITE |(+ (if a b c) x)|))
     (24 24 (:REWRITE DEFAULT-FLOOR-2))
     (24 24 (:REWRITE DEFAULT-FLOOR-1))
     (23 23 (:REWRITE |(floor x 2)| . 2))
     (18 18 (:REWRITE |(< (+ c/d x) y)|))
     (18 18 (:REWRITE |(< (+ (- c) x) y)|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 1
         (:REWRITE M1::NATP-FAST-FLOOR-CLOCK-LEMMA))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE |(floor (+ x r) i)|))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(M1::NATP-FAST-LOG2-LOOP-CLOCK-LEMMA
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-LOG2-LOOP-CLOCK-LEMMA)))
(M1::FAST-LOG2-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-LOG2-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-LOG2-CLOCK-LEMMA
     (11092 796
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11088 1584 (:REWRITE ACL2-NUMBERP-X))
     (3168 792 (:REWRITE RATIONALP-X))
     (3168 792
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1588 796
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1586 1586 (:REWRITE REDUCE-INTEGERP-+))
     (1586 1586 (:REWRITE INTEGERP-MINUS-X))
     (1586 1586 (:META META-INTEGERP-CORRECT))
     (796 796 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (796 796
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (796 796
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (796 796
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (796 796 (:REWRITE |(equal c (/ x))|))
     (796 796 (:REWRITE |(equal c (- x))|))
     (796 796 (:REWRITE |(equal (/ x) c)|))
     (796 796 (:REWRITE |(equal (/ x) (/ y))|))
     (796 796 (:REWRITE |(equal (- x) c)|))
     (796 796 (:REWRITE |(equal (- x) (- y))|))
     (792 792 (:REWRITE REDUCE-RATIONALP-+))
     (792 792 (:REWRITE REDUCE-RATIONALP-*))
     (792 792 (:REWRITE RATIONALP-MINUS-X))
     (792 792 (:META META-RATIONALP-CORRECT))
     (110 32 (:REWRITE DEFAULT-PLUS-2))
     (48 32 (:REWRITE DEFAULT-PLUS-1))
     (30 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (28 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (27 27
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (18 18 (:REWRITE DEFAULT-CDR))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-LOG2-CLOCK-LEMMA
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-LOG2-CLOCK-LEMMA)))
(M1::FAST-EXPT-LOOP-CLOCK)
(M1::FAST-EXPT-LOOP-CLOCK-LEMMA
     (17 15 (:REWRITE DEFAULT-PLUS-2))
     (16 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (16 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (16 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15 (:REWRITE DEFAULT-PLUS-1))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 14 (:REWRITE CONSTANT-<-INTEGERP))
     (14 14
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (14 14
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (14 14
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (14 14
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (14 14 (:REWRITE |(< c (- x))|))
     (14 14
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (14 14
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (14 14
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (14 14
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:REWRITE |(< (/ x) (/ y))|))
     (14 14 (:REWRITE |(< (- x) c)|))
     (14 14 (:REWRITE |(< (- x) (- y))|))
     (14 14 (:REWRITE |(< (* x y) 0)|))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11 (:META META-INTEGERP-CORRECT))
     (9 9 (:REWRITE DEFAULT-TIMES-2))
     (9 9 (:REWRITE DEFAULT-TIMES-1))
     (9 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 2 (:REWRITE |(* y x)|))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::NATP-FAST-EXPT-LOOP-CLOCK-LEMMA
     (2 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-EXPT-LOOP-CLOCK-LEMMA)))
(M1::FAST-EXPT-CLOCK
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-FAST-EXPT-LOOP-CLOCK-LEMMA)))
(M1::FAST-EXPT-CLOCK-LEMMA
     (41606 2996
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (41580 5940 (:REWRITE ACL2-NUMBERP-X))
     (11880 2970 (:REWRITE RATIONALP-X))
     (11880 2970
            (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (5966 2996
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5943 5943 (:REWRITE REDUCE-INTEGERP-+))
     (5943 5943 (:REWRITE INTEGERP-MINUS-X))
     (5943 5943 (:META META-INTEGERP-CORRECT))
     (2996 2996 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2996 2996
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2996 2996
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2996 2996
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2996 2996 (:REWRITE |(equal c (/ x))|))
     (2996 2996 (:REWRITE |(equal c (- x))|))
     (2996 2996 (:REWRITE |(equal (/ x) c)|))
     (2996 2996 (:REWRITE |(equal (/ x) (/ y))|))
     (2996 2996 (:REWRITE |(equal (- x) c)|))
     (2996 2996 (:REWRITE |(equal (- x) (- y))|))
     (2970 2970 (:REWRITE REDUCE-RATIONALP-+))
     (2970 2970 (:REWRITE REDUCE-RATIONALP-*))
     (2970 2970 (:REWRITE RATIONALP-MINUS-X))
     (2970 2970 (:META META-RATIONALP-CORRECT))
     (104 32 (:REWRITE DEFAULT-PLUS-2))
     (62 62 (:REWRITE DEFAULT-CDR))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (31 31
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (29 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (27 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (13 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 11 (:REWRITE |(< (- x) c)|))
     (13 11 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (11 11 (:REWRITE INTEGERP-<-CONSTANT))
     (11 11 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< c (- x))|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-EXPT-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (2 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-EXPT-CLOCK-LEMMA)))
(M1::FAST-NST-IN-LOOP-CLOCK
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION M1::NATP-FAST-EXPT-CLOCK-LEMMA)))
(M1::FAST-NST-IN-LOOP-CLOCK-LEMMA
 (116 10 (:REWRITE DEFAULT-PLUS-2))
 (38 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (29
   29
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (29
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (13 10 (:REWRITE DEFAULT-PLUS-1))
 (10 1 (:REWRITE DEFAULT-TIMES-2))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE DEFAULT-TIMES-1)))
(M1::NATP-FAST-NST-IN-LOOP-CLOCK-LEMMA
 (23 2 (:REWRITE DEFAULT-PLUS-2))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-NST-IN-LOOP-CLOCK-LEMMA))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(M1::FAST-NST-IN-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NST-IN-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NST-IN-CLOCK-LEMMA
     (5544 792 (:REWRITE ACL2-NUMBERP-X))
     (5544 396
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1584 396 (:REWRITE RATIONALP-X))
     (1584 396
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (794 794 (:REWRITE REDUCE-INTEGERP-+))
     (794 794 (:REWRITE INTEGERP-MINUS-X))
     (794 794 (:META META-INTEGERP-CORRECT))
     (792 396
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 396 (:REWRITE REDUCE-RATIONALP-+))
     (396 396 (:REWRITE REDUCE-RATIONALP-*))
     (396 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (396 396
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (396 396 (:REWRITE RATIONALP-MINUS-X))
     (396 396
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE |(equal c (/ x))|))
     (396 396 (:REWRITE |(equal c (- x))|))
     (396 396 (:REWRITE |(equal (/ x) c)|))
     (396 396 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396 (:REWRITE |(equal (- x) c)|))
     (396 396 (:REWRITE |(equal (- x) (- y))|))
     (396 396 (:META META-RATIONALP-CORRECT))
     (92 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (25 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (24 10 (:REWRITE DEFAULT-TIMES-2))
     (23 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NST-IN-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NST-IN-CLOCK-LEMMA)))
(M1::FAST-NSYM-LOOP-CLOCK
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (112 112
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (112 112
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (49 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (49 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (49 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (15
   15
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (15
  15
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION M1::NATP-FAST-EXPT-CLOCK-LEMMA)))
(M1::NSYM-LOOP-CLOCK-LEMMA
 (2293 15 (:REWRITE DEFAULT-PLUS-2))
 (1160 872
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (872 872
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (872 872
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (872 872
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (872 872
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (872 872
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (846 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (846 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (810 17 (:REWRITE DEFAULT-LESS-THAN-1))
 (798 42 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (546 42
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (546 42
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (546 42
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (372 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (354 2 (:REWRITE FLOOR-ZERO . 3))
 (352 2 (:REWRITE FLOOR-ZERO . 4))
 (294 42 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (294 42 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (294 42
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (254 2 (:REWRITE CANCEL-FLOOR-+))
 (227
   227
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (227
  227
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (227 227
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (227
     227
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (227 227
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (227 227
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (146 2 (:REWRITE FLOOR-=-X/Y . 3))
 (142 2 (:REWRITE FLOOR-=-X/Y . 2))
 (140 14 (:REWRITE DEFAULT-TIMES-2))
 (100 10 (:REWRITE DEFAULT-DIVIDE))
 (92 2 (:REWRITE FLOOR-ZERO . 5))
 (86 2 (:REWRITE |(integerp (- x))|))
 (84 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (60 10 (:REWRITE |(/ (expt x n))|))
 (60 8
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (56 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (56 4 (:LINEAR EXPT->=-1-ONE))
 (56 2 (:REWRITE |(* (- x) y)|))
 (53 17 (:REWRITE SIMPLIFY-SUMS-<))
 (53 17 (:REWRITE DEFAULT-LESS-THAN-2))
 (50 2 (:REWRITE FLOOR-ZERO . 2))
 (50 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (48 15 (:REWRITE DEFAULT-PLUS-1))
 (38 12 (:REWRITE DEFAULT-MINUS))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (32 2
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (32 2 (:REWRITE FLOOR-CANCEL-*-CONST))
 (32 2
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (32 2
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (26 26 (:REWRITE DEFAULT-EXPT-2))
 (26 26 (:REWRITE DEFAULT-EXPT-1))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (26 26 (:REWRITE |(expt (- x) n)|))
 (20 2 (:REWRITE DEFAULT-FLOOR-2))
 (17 17 (:REWRITE THE-FLOOR-BELOW))
 (17 17 (:REWRITE THE-FLOOR-ABOVE))
 (17 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (17 17
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< c (- x))|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE |(< (- x) c)|))
 (17 17 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE DEFAULT-TIMES-1))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (10 10 (:REWRITE NORMALIZE-ADDENDS))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE ODD-EXPT-THM))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (4 4 (:LINEAR EXPT-X->=-X))
 (4 4 (:LINEAR EXPT-X->-X))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT->-1-ONE))
 (4 4 (:LINEAR EXPT-<=-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-FLOOR-1))
 (2 2 (:REWRITE |(floor x (- y))| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 1))
 (2 2
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor (- x) y)| . 2))
 (2 2 (:REWRITE |(floor (- x) y)| . 1))
 (2 2
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|)))
(M1::NATP-NSYM-LOOP-CLOCK-LEMMA
 (459 3 (:REWRITE DEFAULT-PLUS-2))
 (240 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (186 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (177 1 (:REWRITE FLOOR-ZERO . 3))
 (176 1 (:REWRITE FLOOR-ZERO . 4))
 (127 1 (:REWRITE CANCEL-FLOOR-+))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (96 96
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (96 96
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (80
   80
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (80
  80
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (76 4 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (73 1 (:REWRITE FLOOR-=-X/Y . 3))
 (71 1 (:REWRITE FLOOR-=-X/Y . 2))
 (60 6 (:REWRITE DEFAULT-TIMES-2))
 (52 4
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (52 4
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (52 4
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (46 1 (:REWRITE FLOOR-ZERO . 5))
 (43 1 (:REWRITE |(integerp (- x))|))
 (42 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (37 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (37 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30 5 (:REWRITE |(/ (expt x n))|))
 (30 4
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 4 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (28 4 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (28 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (28 1 (:REWRITE |(* (- x) y)|))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (24 6 (:REWRITE SIMPLIFY-SUMS-<))
 (24 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 6 (:REWRITE DEFAULT-MINUS))
 (19 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (16 1
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (14 3 (:REWRITE DEFAULT-PLUS-1))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-NSYM-LOOP-CLOCK-LEMMA))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(- (* c x))|)))
(M1::FAST-NSYM-CLOCK (10 5
                         (:TYPE-PRESCRIPTION M1::NATP-NSYM-LOOP-CLOCK-LEMMA))
                     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NSYM-CLOCK-LEMMA
     (5544 792 (:REWRITE ACL2-NUMBERP-X))
     (5544 396
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1584 396 (:REWRITE RATIONALP-X))
     (1584 396
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (794 794 (:REWRITE REDUCE-INTEGERP-+))
     (794 794 (:REWRITE INTEGERP-MINUS-X))
     (794 794 (:META META-INTEGERP-CORRECT))
     (792 396
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 396 (:REWRITE REDUCE-RATIONALP-+))
     (396 396 (:REWRITE REDUCE-RATIONALP-*))
     (396 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (396 396
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (396 396 (:REWRITE RATIONALP-MINUS-X))
     (396 396
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE |(equal c (/ x))|))
     (396 396 (:REWRITE |(equal c (- x))|))
     (396 396 (:REWRITE |(equal (/ x) c)|))
     (396 396 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396 (:REWRITE |(equal (- x) c)|))
     (396 396 (:REWRITE |(equal (- x) (- y))|))
     (396 396 (:META META-RATIONALP-CORRECT))
     (92 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (25 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (24 10 (:REWRITE DEFAULT-TIMES-2))
     (23 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NSYM-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NSYM-CLOCK-LEMMA)))
(M1::FAST-NOP-LOOP-CLOCK
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (112 112
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (112 112
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (49 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (49 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (49 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (49 7
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (15
  15
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::FAST-NOP-LOOP-CLOCK-LEMMA
 (2623 33 (:REWRITE DEFAULT-PLUS-2))
 (1200 912
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (912 912
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (912 912
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (912 912
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (912 912
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (838 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (838 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (836 44 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (802 17 (:REWRITE DEFAULT-LESS-THAN-1))
 (572 44
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (572 44
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (572 44
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (364 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (344 2 (:REWRITE FLOOR-ZERO . 4))
 (318 2 (:REWRITE FLOOR-ZERO . 3))
 (308 44 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (308 44 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (308 44
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (231
  231
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (231 231
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (231
     231
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (231 231
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (231 231
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (226 2 (:REWRITE CANCEL-FLOOR-+))
 (142 2 (:REWRITE FLOOR-=-X/Y . 3))
 (140 14 (:REWRITE DEFAULT-TIMES-2))
 (130 2 (:REWRITE FLOOR-=-X/Y . 2))
 (120 10 (:REWRITE |(/ (expt x n))|))
 (100 10 (:REWRITE DEFAULT-DIVIDE))
 (92 4 (:LINEAR EXPT->-1-ONE))
 (92 2 (:REWRITE FLOOR-ZERO . 5))
 (88 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (66 33 (:REWRITE DEFAULT-PLUS-1))
 (62 2 (:REWRITE |(integerp (- x))|))
 (60 10 (:REWRITE |(- (+ x y))|))
 (56 4 (:LINEAR EXPT->=-1-ONE))
 (53 17 (:REWRITE SIMPLIFY-SUMS-<))
 (53 17 (:REWRITE DEFAULT-LESS-THAN-2))
 (50 2 (:REWRITE FLOOR-ZERO . 2))
 (50 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (48 2 (:REWRITE |(* (- x) y)|))
 (40 22 (:REWRITE DEFAULT-MINUS))
 (32 2
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (32 2 (:REWRITE FLOOR-CANCEL-*-CONST))
 (32 2
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (32 2
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 27 (:REWRITE NORMALIZE-ADDENDS))
 (22 22 (:REWRITE DEFAULT-EXPT-2))
 (22 22 (:REWRITE DEFAULT-EXPT-1))
 (22 22 (:REWRITE |(expt 1/c n)|))
 (22 22 (:REWRITE |(expt (- x) n)|))
 (20 2 (:REWRITE DEFAULT-FLOOR-2))
 (17 17 (:REWRITE THE-FLOOR-BELOW))
 (17 17 (:REWRITE THE-FLOOR-ABOVE))
 (17 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (17 17
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< c (- x))|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE |(< (- x) c)|))
 (17 17 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE DEFAULT-TIMES-1))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:REWRITE ODD-EXPT-THM))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (4 4 (:LINEAR EXPT-X->=-X))
 (4 4 (:LINEAR EXPT-X->-X))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-FLOOR-1))
 (2 2 (:REWRITE |(floor x (- y))| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 1))
 (2 2
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor (- x) y)| . 2))
 (2 2 (:REWRITE |(floor (- x) y)| . 1))
 (2 2
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|)))
(M1::NATP-FAST-NOP-LOOP-CLOCK-LEMMA
 (467 11 (:REWRITE DEFAULT-PLUS-2))
 (240 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (182 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (172 1 (:REWRITE FLOOR-ZERO . 4))
 (159 1 (:REWRITE FLOOR-ZERO . 3))
 (113 1 (:REWRITE CANCEL-FLOOR-+))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (96 96
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (80
  80
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (80 80
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (76 4 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (71 1 (:REWRITE FLOOR-=-X/Y . 3))
 (65 1 (:REWRITE FLOOR-=-X/Y . 2))
 (60 6 (:REWRITE DEFAULT-TIMES-2))
 (60 5 (:REWRITE |(/ (expt x n))|))
 (52 4
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (52 4
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (52 4
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (46 2 (:LINEAR EXPT->-1-ONE))
 (46 1 (:REWRITE FLOOR-ZERO . 5))
 (44 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (33 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (31 1 (:REWRITE |(integerp (- x))|))
 (30 5 (:REWRITE |(- (+ x y))|))
 (28 4 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (28 4 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (28 4
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (24 6 (:REWRITE SIMPLIFY-SUMS-<))
 (24 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 1 (:REWRITE |(* (- x) y)|))
 (22 11 (:REWRITE DEFAULT-PLUS-1))
 (20 11 (:REWRITE DEFAULT-MINUS))
 (16 1
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-NOP-LOOP-CLOCK-LEMMA))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(- (* c x))|)))
(M1::FAST-NOP-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NOP-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NOP-CLOCK-LEMMA
     (5544 792 (:REWRITE ACL2-NUMBERP-X))
     (5544 396
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1584 396 (:REWRITE RATIONALP-X))
     (1584 396
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (794 794 (:REWRITE REDUCE-INTEGERP-+))
     (794 794 (:REWRITE INTEGERP-MINUS-X))
     (794 794 (:META META-INTEGERP-CORRECT))
     (792 396
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 396 (:REWRITE REDUCE-RATIONALP-+))
     (396 396 (:REWRITE REDUCE-RATIONALP-*))
     (396 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (396 396
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (396 396 (:REWRITE RATIONALP-MINUS-X))
     (396 396
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE |(equal c (/ x))|))
     (396 396 (:REWRITE |(equal c (- x))|))
     (396 396 (:REWRITE |(equal (/ x) c)|))
     (396 396 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396 (:REWRITE |(equal (- x) c)|))
     (396 396 (:REWRITE |(equal (- x) (- y))|))
     (396 396 (:META META-RATIONALP-CORRECT))
     (92 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (25 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (24 10 (:REWRITE DEFAULT-TIMES-2))
     (23 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NOP-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NOP-CLOCK-LEMMA)))
(M1::FAST-NST-OUT-LOOP-CLOCK
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (128 128
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::FAST-NST-OUT-LOOP-CLOCK-LEMMA
 (4995 47 (:REWRITE DEFAULT-PLUS-2))
 (1680 1392
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1392 1392
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1392 1392
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1392 1392
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1392 1392
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1292 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1200 20
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1200 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1164 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (884 68
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (884 68
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (884 68
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (476 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (476 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (476 68
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (434 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (414 2 (:REWRITE FLOOR-ZERO . 4))
 (342
  342
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (342 342
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (342
     342
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (342 342
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (342 342
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (318 2 (:REWRITE FLOOR-ZERO . 3))
 (226 2 (:REWRITE CANCEL-FLOOR-+))
 (150 15 (:REWRITE DEFAULT-TIMES-2))
 (142 2 (:REWRITE FLOOR-=-X/Y . 3))
 (130 2 (:REWRITE FLOOR-=-X/Y . 2))
 (120 10 (:REWRITE |(/ (expt x n))|))
 (109 47 (:REWRITE DEFAULT-PLUS-1))
 (100 10 (:REWRITE DEFAULT-DIVIDE))
 (92 4 (:LINEAR EXPT-X->-X))
 (92 4 (:LINEAR EXPT->-1-ONE))
 (92 2 (:REWRITE FLOOR-ZERO . 5))
 (88 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (62 2 (:REWRITE |(integerp (- x))|))
 (60 10 (:REWRITE |(- (+ x y))|))
 (56 20 (:REWRITE SIMPLIFY-SUMS-<))
 (56 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (56 4 (:LINEAR EXPT-X->=-X))
 (56 4 (:LINEAR EXPT->=-1-ONE))
 (50 2 (:REWRITE FLOOR-ZERO . 2))
 (50 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (48 2 (:REWRITE |(* (- x) y)|))
 (40 22 (:REWRITE DEFAULT-MINUS))
 (35 35
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 35 (:REWRITE NORMALIZE-ADDENDS))
 (32 32 (:REWRITE DEFAULT-EXPT-2))
 (32 32 (:REWRITE DEFAULT-EXPT-1))
 (32 32 (:REWRITE |(expt 1/c n)|))
 (32 32 (:REWRITE |(expt (- x) n)|))
 (32 2
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (32 2 (:REWRITE FLOOR-CANCEL-*-CONST))
 (32 2
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (32 2
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (20 2 (:REWRITE DEFAULT-FLOOR-2))
 (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (15 15 (:REWRITE DEFAULT-TIMES-1))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE ODD-EXPT-THM))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-FLOOR-1))
 (2 2 (:REWRITE |(floor x (- y))| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 1))
 (2 2
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor (- x) y)| . 2))
 (2 2 (:REWRITE |(floor (- x) y)| . 1))
 (2 2
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|)))
(M1::NATP-FAST-NST-OUT-LOOP-CLOCK-LEMMA
 (1303 16 (:REWRITE DEFAULT-PLUS-2))
 (340 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (217 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (207 1 (:REWRITE FLOOR-ZERO . 4))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (196 196
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (171 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (159 1 (:REWRITE FLOOR-ZERO . 3))
 (117 9
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (117 9
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (117 9
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (113 1 (:REWRITE CANCEL-FLOOR-+))
 (104
  104
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (104 104
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (104
     104
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (104 104
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (104 104
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (71 1 (:REWRITE FLOOR-=-X/Y . 3))
 (65 1 (:REWRITE FLOOR-=-X/Y . 2))
 (63 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (63 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (63 9
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (60 6 (:REWRITE DEFAULT-TIMES-2))
 (60 5 (:REWRITE |(/ (expt x n))|))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (46 2 (:LINEAR EXPT-X->-X))
 (46 2 (:LINEAR EXPT->-1-ONE))
 (46 1 (:REWRITE FLOOR-ZERO . 5))
 (44 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (41 16 (:REWRITE DEFAULT-PLUS-1))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (33 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (31 1 (:REWRITE |(integerp (- x))|))
 (30 5 (:REWRITE |(- (+ x y))|))
 (28 2 (:LINEAR EXPT-X->=-X))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (24 6 (:REWRITE SIMPLIFY-SUMS-<))
 (24 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 1 (:REWRITE |(* (- x) y)|))
 (20 11 (:REWRITE DEFAULT-MINUS))
 (16 16 (:REWRITE DEFAULT-EXPT-2))
 (16 16 (:REWRITE DEFAULT-EXPT-1))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (16 1
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE NORMALIZE-ADDENDS))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-NST-OUT-LOOP-CLOCK-LEMMA))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(- (* c x))|)))
(M1::FAST-NST-OUT-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NST-OUT-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NST-OUT-CLOCK-LEMMA
     (5544 792 (:REWRITE ACL2-NUMBERP-X))
     (5544 396
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1584 396 (:REWRITE RATIONALP-X))
     (1584 396
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (794 794 (:REWRITE REDUCE-INTEGERP-+))
     (794 794 (:REWRITE INTEGERP-MINUS-X))
     (794 794 (:META META-INTEGERP-CORRECT))
     (792 396
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 396 (:REWRITE REDUCE-RATIONALP-+))
     (396 396 (:REWRITE REDUCE-RATIONALP-*))
     (396 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (396 396
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (396 396 (:REWRITE RATIONALP-MINUS-X))
     (396 396
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE |(equal c (/ x))|))
     (396 396 (:REWRITE |(equal c (- x))|))
     (396 396 (:REWRITE |(equal (/ x) c)|))
     (396 396 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396 (:REWRITE |(equal (- x) c)|))
     (396 396 (:REWRITE |(equal (- x) (- y))|))
     (396 396 (:META META-RATIONALP-CORRECT))
     (92 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (25 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (24 10 (:REWRITE DEFAULT-TIMES-2))
     (23 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NST-OUT-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NST-OUT-CLOCK-LEMMA)))
(M1::FAST-NCAR-LOOP-CLOCK
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::FAST-NCAR-LOOP-CLOCK-LEMMA
 (120 14 (:REWRITE DEFAULT-PLUS-2))
 (38 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (29
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 14 (:REWRITE DEFAULT-PLUS-1))
 (14 5 (:REWRITE DEFAULT-TIMES-2))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT)))
(M1::NATP-FAST-NCAR-LOOP-CLOCK-LEMMA
 (25 4 (:REWRITE DEFAULT-PLUS-2))
 (5 4 (:REWRITE DEFAULT-PLUS-1))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-NCAR-LOOP-CLOCK-LEMMA))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(M1::FAST-NCAR-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NCAR-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NCAR-CLOCK-LEMMA
     (11092 796
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11088 1584 (:REWRITE ACL2-NUMBERP-X))
     (3168 792 (:REWRITE RATIONALP-X))
     (3168 792
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1588 796
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1586 1586 (:REWRITE REDUCE-INTEGERP-+))
     (1586 1586 (:REWRITE INTEGERP-MINUS-X))
     (1586 1586 (:META META-INTEGERP-CORRECT))
     (796 796 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (796 796
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (796 796
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (796 796
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (796 796 (:REWRITE |(equal c (/ x))|))
     (796 796 (:REWRITE |(equal c (- x))|))
     (796 796 (:REWRITE |(equal (/ x) c)|))
     (796 796 (:REWRITE |(equal (/ x) (/ y))|))
     (796 796 (:REWRITE |(equal (- x) c)|))
     (796 796 (:REWRITE |(equal (- x) (- y))|))
     (792 792 (:REWRITE REDUCE-RATIONALP-+))
     (792 792 (:REWRITE REDUCE-RATIONALP-*))
     (792 792 (:REWRITE RATIONALP-MINUS-X))
     (792 792 (:META META-RATIONALP-CORRECT))
     (104 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (28 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (26 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (18 18 (:REWRITE DEFAULT-CDR))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NCAR-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NCAR-CLOCK-LEMMA)))
(M1::FAST-NCDR-LOOP-CLOCK
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::FAST-NCDR-LOOP-CLOCK-LEMMA
 (120 14 (:REWRITE DEFAULT-PLUS-2))
 (38 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (29
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 14 (:REWRITE DEFAULT-PLUS-1))
 (14 5 (:REWRITE DEFAULT-TIMES-2))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT)))
(M1::NATP-FAST-NCDR-LOOP-CLOCK-LEMMA
 (25 4 (:REWRITE DEFAULT-PLUS-2))
 (5 4 (:REWRITE DEFAULT-PLUS-1))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-NCDR-LOOP-CLOCK-LEMMA))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(M1::FAST-NCDR-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NCDR-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NCDR-CLOCK-LEMMA
     (5544 792 (:REWRITE ACL2-NUMBERP-X))
     (5544 396
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1584 396 (:REWRITE RATIONALP-X))
     (1584 396
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (794 794 (:REWRITE REDUCE-INTEGERP-+))
     (794 794 (:REWRITE INTEGERP-MINUS-X))
     (794 794 (:META META-INTEGERP-CORRECT))
     (792 396
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 396 (:REWRITE REDUCE-RATIONALP-+))
     (396 396 (:REWRITE REDUCE-RATIONALP-*))
     (396 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (396 396
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (396 396 (:REWRITE RATIONALP-MINUS-X))
     (396 396
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE |(equal c (/ x))|))
     (396 396 (:REWRITE |(equal c (- x))|))
     (396 396 (:REWRITE |(equal (/ x) c)|))
     (396 396 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396 (:REWRITE |(equal (- x) c)|))
     (396 396 (:REWRITE |(equal (- x) (- y))|))
     (396 396 (:META META-RATIONALP-CORRECT))
     (92 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (25 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (24 10 (:REWRITE DEFAULT-TIMES-2))
     (23 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NCDR-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NCDR-CLOCK-LEMMA)))
(M1::FAST-CURRENT-SYMN-LOOP-CLOCK
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (128 128
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (128 128
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (18 9
     (:TYPE-PRESCRIPTION M1::NATP-FAST-LOG2-CLOCK-LEMMA))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (6 6
    (:TYPE-PRESCRIPTION M1::NATP-FAST-EXPT-CLOCK-LEMMA)))
(M1::FAST-CURRENT-SYMN-LOOP-CLOCK-LEMMA
 (4195 56 (:REWRITE DEFAULT-PLUS-2))
 (1720 1432
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1432 1432
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1432 1432
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1432 1432
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1432 1432
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (1432 1432
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1330 70 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1317 23
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1317 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1281 23 (:REWRITE DEFAULT-LESS-THAN-1))
 (910 70
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (910 70
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (910 70
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (490 70 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (490 70 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (490 70
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (372 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (354 2 (:REWRITE FLOOR-ZERO . 3))
 (352 2 (:REWRITE FLOOR-ZERO . 4))
 (273
   273
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (273
  273
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (273 273
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (273
     273
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (273 273
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (273 273
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (254 2 (:REWRITE CANCEL-FLOOR-+))
 (252 56 (:REWRITE DEFAULT-PLUS-1))
 (150 24 (:REWRITE DEFAULT-TIMES-2))
 (146 2 (:REWRITE FLOOR-=-X/Y . 3))
 (142 2 (:REWRITE FLOOR-=-X/Y . 2))
 (116 2 (:DEFINITION M1::LOG2))
 (106 4 (:REWRITE DEFAULT-FLOOR-RATIO))
 (100 10 (:REWRITE DEFAULT-DIVIDE))
 (92 2 (:REWRITE FLOOR-ZERO . 5))
 (86 2 (:REWRITE |(integerp (- x))|))
 (60 10 (:REWRITE |(/ (expt x n))|))
 (60 8
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (59 23 (:REWRITE SIMPLIFY-SUMS-<))
 (59 23 (:REWRITE DEFAULT-LESS-THAN-2))
 (56 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (56 4 (:LINEAR EXPT->=-1-ONE))
 (56 2 (:REWRITE |(* (- x) y)|))
 (50 2 (:REWRITE FLOOR-ZERO . 2))
 (50 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (50 2 (:REWRITE |(floor x 2)| . 1))
 (42 14 (:REWRITE DEFAULT-MINUS))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (32 2
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (32 2 (:REWRITE FLOOR-CANCEL-*-CONST))
 (32 2
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (32 2
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 26 (:REWRITE DEFAULT-EXPT-2))
 (26 26 (:REWRITE DEFAULT-EXPT-1))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (26 26 (:REWRITE |(expt (- x) n)|))
 (24 24 (:REWRITE DEFAULT-TIMES-1))
 (23 23 (:REWRITE THE-FLOOR-BELOW))
 (23 23 (:REWRITE THE-FLOOR-ABOVE))
 (23 23
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (23 23
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (- x))|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE |(< (- x) c)|))
 (23 23 (:REWRITE |(< (- x) (- y))|))
 (22 4 (:REWRITE DEFAULT-FLOOR-2))
 (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (10 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (8 6 (:REWRITE |(equal (- x) c)|))
 (8 6 (:REWRITE |(equal (- x) (- y))|))
 (8 2 (:REWRITE |(* y x)|))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4 (:REWRITE ODD-EXPT-THM))
 (4 4 (:REWRITE DEFAULT-FLOOR-1))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (4 4 (:LINEAR EXPT-X->=-X))
 (4 4 (:LINEAR EXPT-X->-X))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT->-1-ONE))
 (4 4 (:LINEAR EXPT-<=-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE |(floor x 2)| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 1))
 (2 2
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor (- x) y)| . 2))
 (2 2 (:REWRITE |(floor (- x) y)| . 1))
 (2 2
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|)))
(M1::NATP-FAST-CURRENT-SYMN-LOOP-CLOCK-LEMMA
 (637 15 (:REWRITE DEFAULT-PLUS-2))
 (260 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (186 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (177 1 (:REWRITE FLOOR-ZERO . 3))
 (176 1 (:REWRITE FLOOR-ZERO . 4))
 (127 1 (:REWRITE CANCEL-FLOOR-+))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (116 116
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (116 116
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (95 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (82
   82
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (82
  82
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (82 82
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (82 82
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (82 82
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (82 82
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (73 1 (:REWRITE FLOOR-=-X/Y . 3))
 (71 1 (:REWRITE FLOOR-=-X/Y . 2))
 (65 11 (:REWRITE DEFAULT-TIMES-2))
 (65 5
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (65 5
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (65 5
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (58 1 (:DEFINITION M1::LOG2))
 (53 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (46 1 (:REWRITE FLOOR-ZERO . 5))
 (43 1 (:REWRITE |(integerp (- x))|))
 (37 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (37 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (35 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (35 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (35 5
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (33 15 (:REWRITE DEFAULT-PLUS-1))
 (30 5 (:REWRITE |(/ (expt x n))|))
 (30 4
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (28 1 (:REWRITE |(* (- x) y)|))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (25 1 (:REWRITE |(floor x 2)| . 1))
 (24 6 (:REWRITE SIMPLIFY-SUMS-<))
 (24 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (21 7 (:REWRITE DEFAULT-MINUS))
 (19 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (16 1
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 2 (:REWRITE DEFAULT-FLOOR-2))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 3 (:REWRITE |(equal (- x) c)|))
 (4 3 (:REWRITE |(equal (- x) (- y))|))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-CURRENT-SYMN-LOOP-CLOCK-LEMMA))
 (4 1 (:REWRITE |(* y x)|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(+ c (+ d x))|))
 (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE DEFAULT-FLOOR-1))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE |(floor x 2)| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(- (* c x))|)))
(M1::FAST-CURRENT-SYMN-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-CURRENT-SYMN-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-CURRENT-SYMN-CLOCK-LEMMA
     (16640 1196
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16632 2376 (:REWRITE ACL2-NUMBERP-X))
     (4752 1188 (:REWRITE RATIONALP-X))
     (4752 1188
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (2384 1196
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2378 2378 (:REWRITE REDUCE-INTEGERP-+))
     (2378 2378 (:REWRITE INTEGERP-MINUS-X))
     (2378 2378 (:META META-INTEGERP-CORRECT))
     (1196 1196 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1196 1196
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1196 1196
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1196 1196
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1196 1196 (:REWRITE |(equal c (/ x))|))
     (1196 1196 (:REWRITE |(equal c (- x))|))
     (1196 1196 (:REWRITE |(equal (/ x) c)|))
     (1196 1196 (:REWRITE |(equal (/ x) (/ y))|))
     (1196 1196 (:REWRITE |(equal (- x) c)|))
     (1196 1196 (:REWRITE |(equal (- x) (- y))|))
     (1188 1188 (:REWRITE REDUCE-RATIONALP-+))
     (1188 1188 (:REWRITE REDUCE-RATIONALP-*))
     (1188 1188 (:REWRITE RATIONALP-MINUS-X))
     (1188 1188 (:META META-RATIONALP-CORRECT))
     (104 32 (:REWRITE DEFAULT-PLUS-2))
     (45 32 (:REWRITE DEFAULT-PLUS-1))
     (28 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (26 26 (:REWRITE DEFAULT-CDR))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (26 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 24
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-CURRENT-SYMN-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-CURRENT-SYMN-CLOCK-LEMMA)))
(M1::FAST-NINSTR1-LOOP-CLOCK
     (130 10 (:REWRITE ACL2-NUMBERP-X))
     (82 46 (:REWRITE DEFAULT-PLUS-2))
     (42 26
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (42 26 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (42 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (40 10 (:REWRITE RATIONALP-X))
     (40 10
         (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (34 26 (:REWRITE SIMPLIFY-SUMS-<))
     (33 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (31 19 (:REWRITE |(equal (- x) (- y))|))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (26 26
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (26 26
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 26 (:REWRITE CONSTANT-<-INTEGERP))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< c (- x))|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< (/ x) (/ y))|))
     (26 26 (:REWRITE |(< (- x) c)|))
     (26 26 (:REWRITE |(< (- x) (- y))|))
     (22 22 (:REWRITE REDUCE-INTEGERP-+))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (22 22 (:META META-INTEGERP-CORRECT))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (19 19 (:REWRITE |(equal c (/ x))|))
     (19 19 (:REWRITE |(equal c (- x))|))
     (19 19 (:REWRITE |(equal (/ x) c)|))
     (19 19 (:REWRITE |(equal (/ x) (/ y))|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (16 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 15
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (11 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10 (:META META-RATIONALP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(M1::FAST-NINSTR1-LOOP-CLOCK-LEMMA
     (12302 3118 (:REWRITE DEFAULT-PLUS-2))
     (5367 3118 (:REWRITE DEFAULT-PLUS-1))
     (1423 1423
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1192 341
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1192 341
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1192 341 (:REWRITE DEFAULT-LESS-THAN-1))
     (1023 1023 (:REWRITE FOLD-CONSTS-IN-+))
     (443 233
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (372 233 (:REWRITE |(equal (- x) c)|))
     (372 233 (:REWRITE |(equal (- x) (- y))|))
     (345 341 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (341 341 (:REWRITE THE-FLOOR-BELOW))
     (341 341 (:REWRITE THE-FLOOR-ABOVE))
     (341 341
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (341 341
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (341 341 (:REWRITE SIMPLIFY-SUMS-<))
     (341 341
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (341 341
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (341 341
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (341 341
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (341 341 (:REWRITE INTEGERP-<-CONSTANT))
     (341 341 (:REWRITE DEFAULT-LESS-THAN-2))
     (341 341 (:REWRITE CONSTANT-<-INTEGERP))
     (341 341
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (341 341
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (341 341
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (341 341
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (341 341 (:REWRITE |(< c (- x))|))
     (341 341
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (341 341
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (341 341
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (341 341
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (341 341 (:REWRITE |(< (/ x) 0)|))
     (341 341 (:REWRITE |(< (/ x) (/ y))|))
     (341 341 (:REWRITE |(< (- x) c)|))
     (341 341 (:REWRITE |(< (- x) (- y))|))
     (341 341 (:REWRITE |(< (* x y) 0)|))
     (287 130 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (251 112 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (251 112 (:REWRITE DEFAULT-MINUS))
     (233 233
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (233 233
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (233 233
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (233 233 (:REWRITE |(equal c (/ x))|))
     (233 233 (:REWRITE |(equal c (- x))|))
     (233 233 (:REWRITE |(equal (/ x) c)|))
     (233 233 (:REWRITE |(equal (/ x) (/ y))|))
     (181 181 (:REWRITE |(< (+ c/d x) y)|))
     (181 181 (:REWRITE |(< (+ (- c) x) y)|))
     (106 106 (:REWRITE |(equal (+ (- c) x) y)|))
     (75 15 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (50 50 (:REWRITE REDUCE-INTEGERP-+))
     (50 50 (:REWRITE INTEGERP-MINUS-X))
     (50 50 (:META META-INTEGERP-CORRECT))
     (30 30
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(M1::NATP-FAST-NINSTR1-LOOP-CLOCK-LEMMA
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NINSTR1-LOOP-CLOCK-LEMMA)))
(M1::FAST-NINSTR1-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NINSTR1-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NINSTR1-CLOCK-LEMMA
     (11092 796
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11088 1584 (:REWRITE ACL2-NUMBERP-X))
     (3168 792 (:REWRITE RATIONALP-X))
     (3168 792
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1588 1588 (:REWRITE REDUCE-INTEGERP-+))
     (1588 1588 (:REWRITE INTEGERP-MINUS-X))
     (1588 1588 (:META META-INTEGERP-CORRECT))
     (1588 796
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (796 796 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (796 796
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (796 796
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (796 796
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (796 796 (:REWRITE |(equal c (/ x))|))
     (796 796 (:REWRITE |(equal c (- x))|))
     (796 796 (:REWRITE |(equal (/ x) c)|))
     (796 796 (:REWRITE |(equal (/ x) (/ y))|))
     (796 796 (:REWRITE |(equal (- x) c)|))
     (796 796 (:REWRITE |(equal (- x) (- y))|))
     (792 792 (:REWRITE REDUCE-RATIONALP-+))
     (792 792 (:REWRITE REDUCE-RATIONALP-*))
     (792 792 (:REWRITE RATIONALP-MINUS-X))
     (792 792 (:META META-RATIONALP-CORRECT))
     (158 38 (:REWRITE DEFAULT-PLUS-2))
     (60 38 (:REWRITE DEFAULT-PLUS-1))
     (34 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (32 32
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (32 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE DEFAULT-CDR))
     (14 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 12 (:REWRITE |(< (- x) c)|))
     (14 12 (:REWRITE |(< (- x) (- y))|))
     (14 2 (:DEFINITION LEN))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (12 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (12 12 (:REWRITE INTEGERP-<-CONSTANT))
     (12 12 (:REWRITE CONSTANT-<-INTEGERP))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (12 12 (:REWRITE |(< c (- x))|))
     (12 12
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (12 12 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NINSTR1-CLOCK-LEMMA
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NINSTR1-CLOCK-LEMMA)))
(M1::FAST-NEW-TAPE2-LOOP-CLOCK
     (156 78
          (:TYPE-PRESCRIPTION M1::NATP-FAST-CURRENT-SYMN-CLOCK-LEMMA))
     (100 50
          (:TYPE-PRESCRIPTION M1::NATP-FAST-LOG2-CLOCK-LEMMA)))
(M1::FAST-NEW-TAPE2-LOOP-CLOCK-LEMMA
     (928 363 (:REWRITE DEFAULT-PLUS-2))
     (529 363 (:REWRITE DEFAULT-PLUS-1))
     (348 6 (:DEFINITION M1::LOG2))
     (182 66
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (182 66 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (182 66 (:REWRITE DEFAULT-LESS-THAN-1))
     (176 176
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (150 6 (:REWRITE |(floor x 2)| . 1))
     (76 76 (:REWRITE FOLD-CONSTS-IN-+))
     (66 66 (:REWRITE THE-FLOOR-BELOW))
     (66 66 (:REWRITE THE-FLOOR-ABOVE))
     (66 66
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (66 66
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (66 66 (:REWRITE SIMPLIFY-SUMS-<))
     (66 66 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (66 66
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (66 66
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (66 66
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (66 66
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (66 66 (:REWRITE INTEGERP-<-CONSTANT))
     (66 66 (:REWRITE DEFAULT-LESS-THAN-2))
     (66 66 (:REWRITE CONSTANT-<-INTEGERP))
     (66 66
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (66 66
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (66 66
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (66 66
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (66 66 (:REWRITE |(< c (- x))|))
     (66 66
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (66 66
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (66 66
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (66 66
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (66 66 (:REWRITE |(< (/ x) 0)|))
     (66 66 (:REWRITE |(< (/ x) (/ y))|))
     (66 66 (:REWRITE |(< (- x) c)|))
     (66 66 (:REWRITE |(< (- x) (- y))|))
     (66 66 (:REWRITE |(< (* x y) 0)|))
     (66 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (42 34
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (40 34 (:REWRITE |(equal (- x) c)|))
     (40 34 (:REWRITE |(equal (- x) (- y))|))
     (39 39 (:REWRITE |(< (+ c/d x) y)|))
     (39 39 (:REWRITE |(< (+ (- c) x) y)|))
     (34 34
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (34 34
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (34 34
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (34 34 (:REWRITE |(equal c (/ x))|))
     (34 34 (:REWRITE |(equal c (- x))|))
     (34 34 (:REWRITE |(equal (/ x) c)|))
     (34 34 (:REWRITE |(equal (/ x) (/ y))|))
     (34 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (30 30 (:REWRITE DEFAULT-TIMES-2))
     (30 30 (:REWRITE DEFAULT-TIMES-1))
     (24 24
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 6 (:REWRITE |(* y x)|))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (14 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 8 (:REWRITE DEFAULT-MINUS))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE |(floor x 2)| . 2)))
(M1::NATP-FAST-NEW-TAPE2-LOOP-CLOCK-LEMMA
     (461 180 (:REWRITE DEFAULT-PLUS-2))
     (263 180 (:REWRITE DEFAULT-PLUS-1))
     (174 3 (:DEFINITION M1::LOG2))
     (88 88
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (75 3 (:REWRITE |(floor x 2)| . 1))
     (38 38 (:REWRITE FOLD-CONSTS-IN-+))
     (33 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (21 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 17 (:REWRITE |(equal (- x) c)|))
     (20 17 (:REWRITE |(equal (- x) (- y))|))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (17 17
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (17 17 (:REWRITE |(equal c (/ x))|))
     (17 17 (:REWRITE |(equal c (- x))|))
     (17 17 (:REWRITE |(equal (/ x) c)|))
     (17 17 (:REWRITE |(equal (/ x) (/ y))|))
     (17 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 15 (:REWRITE DEFAULT-TIMES-2))
     (15 15 (:REWRITE DEFAULT-TIMES-1))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 3 (:REWRITE |(* y x)|))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (7 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (7 4 (:REWRITE DEFAULT-MINUS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NEW-TAPE2-LOOP-CLOCK-LEMMA))
     (3 3 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE DEFAULT-FLOOR-1))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|)))
(M1::FAST-NEW-TAPE2-CLOCK
     (10 5
         (:TYPE-PRESCRIPTION M1::NATP-FAST-NEW-TAPE2-LOOP-CLOCK-LEMMA))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-NEW-TAPE2-CLOCK-LEMMA
     (5544 792 (:REWRITE ACL2-NUMBERP-X))
     (5544 396
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1584 396 (:REWRITE RATIONALP-X))
     (1584 396
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (795 795 (:REWRITE REDUCE-INTEGERP-+))
     (795 795 (:REWRITE INTEGERP-MINUS-X))
     (795 795 (:META META-INTEGERP-CORRECT))
     (792 396
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 396 (:REWRITE REDUCE-RATIONALP-+))
     (396 396 (:REWRITE REDUCE-RATIONALP-*))
     (396 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (396 396
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (396 396 (:REWRITE RATIONALP-MINUS-X))
     (396 396
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE |(equal c (/ x))|))
     (396 396 (:REWRITE |(equal c (- x))|))
     (396 396 (:REWRITE |(equal (/ x) c)|))
     (396 396 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396 (:REWRITE |(equal (- x) c)|))
     (396 396 (:REWRITE |(equal (- x) (- y))|))
     (396 396 (:META META-RATIONALP-CORRECT))
     (120 38 (:REWRITE DEFAULT-PLUS-2))
     (52 38 (:REWRITE DEFAULT-PLUS-1))
     (28 28
         (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (26 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 10 (:REWRITE DEFAULT-TIMES-2))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:DEFINITION LEN))
     (13 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 11 (:REWRITE |(< (- x) c)|))
     (13 11 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (11 11 (:REWRITE INTEGERP-<-CONSTANT))
     (11 11 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< c (- x))|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(* (- x) y)|)))
(M1::NATP-FAST-NEW-TAPE2-CLOCK-LEMMA
     (5 5
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-FAST-NEW-TAPE2-CLOCK-LEMMA)))
(M1::FAST-TMI3-LOOP-CLOCK
 (44
   44
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (44
  44
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(M1::FAST-TMI3-LOOP-CLOCK-LEMMA
 (51699 2859 (:REWRITE DEFAULT-PLUS-2))
 (37698 581 (:DEFINITION M1::NINSTR))
 (7929 2859 (:REWRITE DEFAULT-PLUS-1))
 (5810 2905
       (:TYPE-PRESCRIPTION M1::NATP-NST-IN))
 (5700 1868
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5695 1868
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5643 1012
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5598 1012
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2905 2905 (:TYPE-PRESCRIPTION M1::NSYM))
 (2905 2905 (:TYPE-PRESCRIPTION M1::NATP-NCAR))
 (2546
   2546
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2546
  2546
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2546
      2546
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2546
     2546
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2546 2546
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2546 2546
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2045 71 (:REWRITE ODD-EXPT-THM))
 (1881 1881
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1868 1868
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1868 1868 (:REWRITE |(equal c (/ x))|))
 (1868 1868 (:REWRITE |(equal c (- x))|))
 (1868 1868 (:REWRITE |(equal (/ x) c)|))
 (1868 1868 (:REWRITE |(equal (/ x) (/ y))|))
 (1868 1868 (:REWRITE |(equal (- x) c)|))
 (1868 1868 (:REWRITE |(equal (- x) (- y))|))
 (1759 1012
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1690 1690
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1666 1012 (:REWRITE SIMPLIFY-SUMS-<))
 (1663 1015 (:REWRITE DEFAULT-LESS-THAN-2))
 (1420 1420 (:REWRITE FOLD-CONSTS-IN-+))
 (1015 1015 (:REWRITE THE-FLOOR-BELOW))
 (1015 1015 (:REWRITE THE-FLOOR-ABOVE))
 (1012 1012
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1012 1012
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1012 1012
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1012 1012 (:REWRITE INTEGERP-<-CONSTANT))
 (1012 1012 (:REWRITE CONSTANT-<-INTEGERP))
 (1012 1012
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1012 1012
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1012 1012
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1012 1012
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1012 1012 (:REWRITE |(< c (- x))|))
 (1012 1012
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1012 1012
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1012 1012
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1012 1012
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1012 1012 (:REWRITE |(< (/ x) (/ y))|))
 (1012 1012 (:REWRITE |(< (- x) c)|))
 (1012 1012 (:REWRITE |(< (- x) (- y))|))
 (934 934 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (806 26 (:LINEAR EXPT-<=-1-TWO))
 (780 26 (:LINEAR EXPT->-1-ONE))
 (740 740
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (740 740
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (740 740 (:REWRITE |(< (/ x) 0)|))
 (740 740 (:REWRITE |(< (* x y) 0)|))
 (676 26 (:LINEAR EXPT-X->=-X))
 (676 26 (:LINEAR EXPT-X->-X))
 (342 342 (:REWRITE |(< (+ c/d x) y)|))
 (342 342 (:REWRITE |(< (+ (- c) x) y)|))
 (211 211 (:REWRITE REDUCE-INTEGERP-+))
 (211 211 (:REWRITE INTEGERP-MINUS-X))
 (211 211 (:META META-INTEGERP-CORRECT))
 (196 196 (:TYPE-PRESCRIPTION M1::!NOP))
 (149 149 (:REWRITE DEFAULT-EXPT-2))
 (149 149 (:REWRITE DEFAULT-EXPT-1))
 (149 149 (:REWRITE |(expt 1/c n)|))
 (149 149 (:REWRITE |(expt (- x) n)|))
 (131 131
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (131 131
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (131 131 (:REWRITE |(< 0 (/ x))|))
 (131 131 (:REWRITE |(< 0 (* x y))|))
 (122 8 (:REWRITE ACL2-NUMBERP-X))
 (52 52
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (52 52
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (52 52
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (40 40 (:REWRITE |(equal (+ (- c) x) y)|))
 (38 8 (:REWRITE RATIONALP-X))
 (38 8
     (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (26 26
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (26 26 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (26 26 (:LINEAR EXPT-LINEAR-UPPER-<))
 (26 26 (:LINEAR EXPT-LINEAR-LOWER-<))
 (26 26 (:LINEAR EXPT->=-1-TWO))
 (26 26 (:LINEAR EXPT->-1-TWO))
 (26 26 (:LINEAR EXPT-<=-1-ONE))
 (26 26 (:LINEAR EXPT-<-1-TWO))
 (26 26 (:LINEAR EXPT-<-1-ONE))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (13 13 (:REWRITE |(< y (+ (- c) x))|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:META META-RATIONALP-CORRECT)))
(M1::NATP-FAST-TMI3-LOOP-CLOCK-LEMMA
 (33777 1184 (:REWRITE DEFAULT-PLUS-2))
 (10815 160 (:DEFINITION M1::NINSTR))
 (4542 1184 (:REWRITE DEFAULT-PLUS-1))
 (1600 800
       (:TYPE-PRESCRIPTION M1::NATP-NST-IN))
 (1496 496
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1496 496
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1443 496 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1154
   1154
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1154
  1154
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1154
      1154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1154
     1154
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1154 1154
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1154 1154
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (892 28 (:REWRITE ODD-EXPT-THM))
 (800 800 (:TYPE-PRESCRIPTION M1::NSYM))
 (800 800 (:TYPE-PRESCRIPTION M1::NATP-NCAR))
 (688 688
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (563 563 (:REWRITE FOLD-CONSTS-IN-+))
 (500 500
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (496 496
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (496 496 (:REWRITE |(equal c (/ x))|))
 (496 496 (:REWRITE |(equal c (- x))|))
 (496 496 (:REWRITE |(equal (/ x) c)|))
 (496 496 (:REWRITE |(equal (/ x) (/ y))|))
 (496 496 (:REWRITE |(equal (- x) c)|))
 (496 496 (:REWRITE |(equal (- x) (- y))|))
 (494 183
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (482 183
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (465 15 (:LINEAR EXPT-<=-1-TWO))
 (459 183 (:REWRITE SIMPLIFY-SUMS-<))
 (453 183
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (450 15 (:LINEAR EXPT->-1-ONE))
 (435 183 (:REWRITE DEFAULT-LESS-THAN-2))
 (408 177 (:REWRITE ZP-OPEN))
 (390 15 (:LINEAR EXPT-X->=-X))
 (390 15 (:LINEAR EXPT-X->-X))
 (242 183 (:REWRITE DEFAULT-LESS-THAN-1))
 (183 183 (:REWRITE THE-FLOOR-BELOW))
 (183 183 (:REWRITE THE-FLOOR-ABOVE))
 (183 183
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (183 183
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (183 183
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (183 183 (:REWRITE INTEGERP-<-CONSTANT))
 (183 183 (:REWRITE CONSTANT-<-INTEGERP))
 (183 183
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (183 183
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (183 183
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (183 183
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (183 183 (:REWRITE |(< c (- x))|))
 (183 183
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (183 183
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (183 183
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (183 183
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (183 183 (:REWRITE |(< (/ x) (/ y))|))
 (183 183 (:REWRITE |(< (- x) c)|))
 (183 183 (:REWRITE |(< (- x) (- y))|))
 (138 138 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (75 75 (:REWRITE DEFAULT-EXPT-2))
 (75 75 (:REWRITE DEFAULT-EXPT-1))
 (75 75 (:REWRITE |(expt 1/c n)|))
 (75 75 (:REWRITE |(expt (- x) n)|))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (65 65 (:REWRITE INTEGERP-MINUS-X))
 (65 65 (:REWRITE |(< 0 (/ x))|))
 (65 65 (:REWRITE |(< 0 (* x y))|))
 (59 59
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (59 59
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (59 59 (:REWRITE |(< (/ x) 0)|))
 (59 59 (:REWRITE |(< (* x y) 0)|))
 (58 58 (:META META-INTEGERP-CORRECT))
 (32 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 30
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (30 30
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (30 30
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (15 15
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (15 15 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (15 15 (:LINEAR EXPT-LINEAR-UPPER-<))
 (15 15 (:LINEAR EXPT-LINEAR-LOWER-<))
 (15 15 (:LINEAR EXPT->=-1-TWO))
 (15 15 (:LINEAR EXPT->-1-TWO))
 (15 15 (:LINEAR EXPT-<=-1-ONE))
 (15 15 (:LINEAR EXPT-<-1-TWO))
 (15 15 (:LINEAR EXPT-<-1-ONE))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-TMI3-LOOP-CLOCK-LEMMA))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::FAST-TMI3-CLOCK
     (18 9
         (:TYPE-PRESCRIPTION M1::NATP-FAST-TMI3-LOOP-CLOCK-LEMMA))
     (9 9 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-TMI3-CLOCK-LEMMA
 (5626 418
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5572 796 (:REWRITE ACL2-NUMBERP-X))
 (1592 398 (:REWRITE RATIONALP-X))
 (1592 398
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (850 418
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (801 801 (:REWRITE REDUCE-INTEGERP-+))
 (801 801 (:REWRITE INTEGERP-MINUS-X))
 (801 801 (:META META-INTEGERP-CORRECT))
 (448 418 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (430 2 (:DEFINITION M1::TMI3))
 (418 418
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (418 418
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (418 418
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (418 418 (:REWRITE |(equal c (/ x))|))
 (418 418 (:REWRITE |(equal c (- x))|))
 (418 418 (:REWRITE |(equal (/ x) c)|))
 (418 418 (:REWRITE |(equal (/ x) (/ y))|))
 (418 418 (:REWRITE |(equal (- x) c)|))
 (418 418 (:REWRITE |(equal (- x) (- y))|))
 (398 398 (:REWRITE REDUCE-RATIONALP-+))
 (398 398 (:REWRITE REDUCE-RATIONALP-*))
 (398 398 (:REWRITE RATIONALP-MINUS-X))
 (398 398 (:META META-RATIONALP-CORRECT))
 (378 6 (:DEFINITION M1::NINSTR))
 (138 42 (:REWRITE DEFAULT-PLUS-2))
 (83
   83
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (83
  83
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (60 42 (:REWRITE DEFAULT-PLUS-1))
 (60 30 (:TYPE-PRESCRIPTION M1::NATP-NST-IN))
 (48 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 38
     (:TYPE-PRESCRIPTION M1::CURRENT-SYMN))
 (38 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (31 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (31 1 (:REWRITE ODD-EXPT-THM))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 30 (:TYPE-PRESCRIPTION M1::NSYM))
 (30 30 (:TYPE-PRESCRIPTION M1::NATP-NCAR))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (27 18 (:REWRITE SIMPLIFY-SUMS-<))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (24 10 (:REWRITE DEFAULT-TIMES-2))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 20 (:REWRITE |(< (- x) c)|))
 (22 20 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 8
     (:TYPE-PRESCRIPTION M1::INTEGERP-NINSTR))
 (14 2 (:DEFINITION LEN))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE ZP-OPEN))
 (8 4 (:REWRITE DEFAULT-MINUS))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NATP-FAST-TMI3-CLOCK-LEMMA
 (2813 209
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2786 398 (:REWRITE ACL2-NUMBERP-X))
 (796 199 (:REWRITE RATIONALP-X))
 (796 199
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (425 209
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (403 403 (:REWRITE REDUCE-INTEGERP-+))
 (403 403 (:REWRITE INTEGERP-MINUS-X))
 (403 403 (:META META-INTEGERP-CORRECT))
 (224 209 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (215 1 (:DEFINITION M1::TMI3))
 (209 209
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (209 209
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (209 209
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (209 209 (:REWRITE |(equal c (/ x))|))
 (209 209 (:REWRITE |(equal c (- x))|))
 (209 209 (:REWRITE |(equal (/ x) c)|))
 (209 209 (:REWRITE |(equal (/ x) (/ y))|))
 (209 209 (:REWRITE |(equal (- x) c)|))
 (209 209 (:REWRITE |(equal (- x) (- y))|))
 (199 199 (:REWRITE REDUCE-RATIONALP-+))
 (199 199 (:REWRITE REDUCE-RATIONALP-*))
 (199 199 (:REWRITE RATIONALP-MINUS-X))
 (199 199 (:META META-RATIONALP-CORRECT))
 (189 3 (:DEFINITION M1::NINSTR))
 (185
   185
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (185
  185
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (185
     185
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (93 3 (:LINEAR EXPT-<=-1-TWO))
 (90 3 (:LINEAR EXPT->-1-ONE))
 (78 3 (:LINEAR EXPT-X->=-X))
 (78 3 (:LINEAR EXPT-X->-X))
 (69 21 (:REWRITE DEFAULT-PLUS-2))
 (39 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (32 21
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (31 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (31 1 (:REWRITE ODD-EXPT-THM))
 (30 21 (:REWRITE DEFAULT-PLUS-1))
 (30 15 (:TYPE-PRESCRIPTION M1::NATP-NST-IN))
 (29 20 (:REWRITE SIMPLIFY-SUMS-<))
 (22 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 21 (:REWRITE |(< (- x) c)|))
 (22 21 (:REWRITE |(< (- x) (- y))|))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (- x))|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (19 19
     (:TYPE-PRESCRIPTION M1::CURRENT-SYMN))
 (15 15 (:TYPE-PRESCRIPTION M1::NSYM))
 (15 15 (:TYPE-PRESCRIPTION M1::NATP-NCAR))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 5 (:REWRITE DEFAULT-TIMES-2))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 4
    (:TYPE-PRESCRIPTION M1::INTEGERP-NINSTR))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (7 1 (:DEFINITION LEN))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE ZP-OPEN))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-TMI3-CLOCK-LEMMA))
 (4 2 (:REWRITE DEFAULT-MINUS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-TWO))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(M1::FAST-MAIN-LOOP-CLOCK
     (8 4
        (:TYPE-PRESCRIPTION M1::NATP-FAST-TMI3-CLOCK-LEMMA))
     (4 4 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-MAIN-LOOP-CLOCK-LEMMA
 (90
   90
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (90
  90
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (62 2 (:REWRITE ODD-EXPT-THM))
 (41 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (34 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (34 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32 14 (:REWRITE SIMPLIFY-SUMS-<))
 (32 14 (:REWRITE DEFAULT-LESS-THAN-2))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (16 14 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (14 14 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE CONSTANT-<-INTEGERP))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< c (- x))|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (14 14 (:REWRITE |(< (- x) (- y))|))
 (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE DEFAULT-PLUS-2))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NATP-FAST-MAIN-LOOP-CLOCK-LEMMA
 (36
   36
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (36
  36
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-MAIN-LOOP-CLOCK-LEMMA)))
(M1::FAST-MAIN-CLOCK
     (18 9
         (:TYPE-PRESCRIPTION M1::NATP-FAST-MAIN-LOOP-CLOCK-LEMMA))
     (9 9 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-MAIN-CLOCK-LEMMA
 (5626 418
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5572 796 (:REWRITE ACL2-NUMBERP-X))
 (1592 398 (:REWRITE RATIONALP-X))
 (1592 398
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (850 418
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (801 801 (:REWRITE REDUCE-INTEGERP-+))
 (801 801 (:REWRITE INTEGERP-MINUS-X))
 (801 801 (:META META-INTEGERP-CORRECT))
 (448 418 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (430 2 (:DEFINITION M1::TMI3))
 (418 418
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (418 418
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (418 418
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (418 418 (:REWRITE |(equal c (/ x))|))
 (418 418 (:REWRITE |(equal c (- x))|))
 (418 418 (:REWRITE |(equal (/ x) c)|))
 (418 418 (:REWRITE |(equal (/ x) (/ y))|))
 (418 418 (:REWRITE |(equal (- x) c)|))
 (418 418 (:REWRITE |(equal (- x) (- y))|))
 (398 398 (:REWRITE REDUCE-RATIONALP-+))
 (398 398 (:REWRITE REDUCE-RATIONALP-*))
 (398 398 (:REWRITE RATIONALP-MINUS-X))
 (398 398 (:META META-RATIONALP-CORRECT))
 (378 6 (:DEFINITION M1::NINSTR))
 (138 42 (:REWRITE DEFAULT-PLUS-2))
 (83
   83
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (83
  83
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (60 42 (:REWRITE DEFAULT-PLUS-1))
 (60 30 (:TYPE-PRESCRIPTION M1::NATP-NST-IN))
 (48 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 38
     (:TYPE-PRESCRIPTION M1::CURRENT-SYMN))
 (38 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (31 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (31 1 (:REWRITE ODD-EXPT-THM))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 30 (:TYPE-PRESCRIPTION M1::NSYM))
 (30 30 (:TYPE-PRESCRIPTION M1::NATP-NCAR))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (27 18 (:REWRITE SIMPLIFY-SUMS-<))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (24 10 (:REWRITE DEFAULT-TIMES-2))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 20 (:REWRITE |(< (- x) c)|))
 (22 20 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 8
     (:TYPE-PRESCRIPTION M1::INTEGERP-NINSTR))
 (14 2 (:DEFINITION LEN))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE ZP-OPEN))
 (8 4 (:REWRITE DEFAULT-MINUS))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NATP-FAST-MAIN-CLOCK-LEMMA
 (2813 209
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2786 398 (:REWRITE ACL2-NUMBERP-X))
 (796 199 (:REWRITE RATIONALP-X))
 (796 199
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (425 209
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (403 403 (:REWRITE REDUCE-INTEGERP-+))
 (403 403 (:REWRITE INTEGERP-MINUS-X))
 (403 403 (:META META-INTEGERP-CORRECT))
 (224 209 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (215 1 (:DEFINITION M1::TMI3))
 (209 209
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (209 209
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (209 209
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (209 209 (:REWRITE |(equal c (/ x))|))
 (209 209 (:REWRITE |(equal c (- x))|))
 (209 209 (:REWRITE |(equal (/ x) c)|))
 (209 209 (:REWRITE |(equal (/ x) (/ y))|))
 (209 209 (:REWRITE |(equal (- x) c)|))
 (209 209 (:REWRITE |(equal (- x) (- y))|))
 (199 199 (:REWRITE REDUCE-RATIONALP-+))
 (199 199 (:REWRITE REDUCE-RATIONALP-*))
 (199 199 (:REWRITE RATIONALP-MINUS-X))
 (199 199 (:META META-RATIONALP-CORRECT))
 (189 3 (:DEFINITION M1::NINSTR))
 (185
   185
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (185
  185
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (185
     185
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (93 3 (:LINEAR EXPT-<=-1-TWO))
 (90 3 (:LINEAR EXPT->-1-ONE))
 (78 3 (:LINEAR EXPT-X->=-X))
 (78 3 (:LINEAR EXPT-X->-X))
 (69 21 (:REWRITE DEFAULT-PLUS-2))
 (39 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (32 21
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (31 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (31 1 (:REWRITE ODD-EXPT-THM))
 (30 21 (:REWRITE DEFAULT-PLUS-1))
 (30 15 (:TYPE-PRESCRIPTION M1::NATP-NST-IN))
 (29 20 (:REWRITE SIMPLIFY-SUMS-<))
 (22 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 21 (:REWRITE |(< (- x) c)|))
 (22 21 (:REWRITE |(< (- x) (- y))|))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (- x))|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (19 19
     (:TYPE-PRESCRIPTION M1::CURRENT-SYMN))
 (15 15 (:TYPE-PRESCRIPTION M1::NSYM))
 (15 15 (:TYPE-PRESCRIPTION M1::NATP-NCAR))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 5 (:REWRITE DEFAULT-TIMES-2))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 4
    (:TYPE-PRESCRIPTION M1::INTEGERP-NINSTR))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (7 1 (:DEFINITION LEN))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE ZP-OPEN))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-MAIN-CLOCK-LEMMA))
 (4 2 (:REWRITE DEFAULT-MINUS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-TWO))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(M1::FAST-PSI-CLOCK (8 4
                       (:TYPE-PRESCRIPTION M1::NATP-FAST-MAIN-CLOCK-LEMMA))
                    (4 4 (:TYPE-PRESCRIPTION NATP)))
(M1::FAST-PSI-CLOCK-THM
 (85
   85
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (85
  85
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (85 85
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (85 85
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (85 85
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (85 85
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (31 1 (:REWRITE ODD-EXPT-THM))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (23 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (23 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (21 12 (:REWRITE SIMPLIFY-SUMS-<))
 (21 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (14 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE DEFAULT-PLUS-2))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NATP-FAST-PSI-CLOCK-THM
 (36
   36
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (36
  36
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 2
    (:TYPE-PRESCRIPTION M1::NATP-FAST-PSI-CLOCK-THM)))
(M1::FIND-K! (12 6
                 (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
             (6 6 (:TYPE-PRESCRIPTION M1::NATP-MAP)))
(M1::FIND-K-IS-FIND-K!
 (5808 8 (:DEFINITION M1::TM-TO-TM1))
 (4449 289 (:REWRITE DEFAULT-CDR))
 (4300 52 (:REWRITE M1::CONSP-ASSOC))
 (4024 56
       (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
 (4012 58 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
 (3546 5 (:DEFINITION M1::MAX-WIDTH1))
 (2522 10 (:DEFINITION M1::LOG2))
 (2180 28 (:DEFINITION ALISTP))
 (1604 52 (:DEFINITION ASSOC-EQUAL))
 (1224 216 (:REWRITE ACL2-NUMBERP-X))
 (1196 103
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (873 10 (:DEFINITION MAX))
 (732 1 (:DEFINITION M1::TURING-MACHINEP))
 (728 1 (:DEFINITION M1::TURING-4-TUPLE))
 (670 14 (:DEFINITION MEMBER-EQUAL))
 (492 492 (:REWRITE DEFAULT-CAR))
 (455 317 (:REWRITE INTEGERP-MINUS-X))
 (428 3 (:DEFINITION M1::SYMP))
 (408 6 (:REWRITE FLOOR-ZERO . 3))
 (375 5 (:REWRITE |(< x (if a b c))|))
 (350 10 (:REWRITE ZP-OPEN))
 (336 84 (:REWRITE RATIONALP-X))
 (336 84
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (318 6 (:REWRITE CANCEL-FLOOR-+))
 (311 311 (:REWRITE REDUCE-INTEGERP-+))
 (311 311 (:META META-INTEGERP-CORRECT))
 (310 2
      (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
 (304 2 (:DEFINITION M1::HALF-TAPE))
 (290 290
      (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
 (285 285 (:TYPE-PRESCRIPTION M1::LOG2))
 (254 1 (:DEFINITION M1::OPERATIONP))
 (206 157 (:REWRITE DEFAULT-LESS-THAN-2))
 (205 152
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (205 152
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (201 157 (:REWRITE DEFAULT-LESS-THAN-1))
 (188 103
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (180 6 (:REWRITE FLOOR-ZERO . 4))
 (180 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (177 152 (:REWRITE SIMPLIFY-SUMS-<))
 (159 1 (:DEFINITION TRUE-LISTP))
 (158 152
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (158 152
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (157 157 (:REWRITE THE-FLOOR-BELOW))
 (157 157 (:REWRITE THE-FLOOR-ABOVE))
 (153 5
      (:REWRITE M1::LOG2-IMPLIES-EXPT-UPPERBOUND))
 (152 152
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (152 152
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (152 152 (:REWRITE INTEGERP-<-CONSTANT))
 (152 152 (:REWRITE CONSTANT-<-INTEGERP))
 (152 152
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (152 152
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (152 152
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (152 152
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (152 152 (:REWRITE |(< c (- x))|))
 (152 152
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (152 152
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (152 152
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (152 152
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (152 152 (:REWRITE |(< (/ x) (/ y))|))
 (152 152 (:REWRITE |(< (- x) c)|))
 (152 152 (:REWRITE |(< (- x) (- y))|))
 (151 103 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (140 140 (:TYPE-PRESCRIPTION ALISTP))
 (136 34 (:REWRITE |(* y x)|))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (132 6 (:REWRITE FLOOR-=-X/Y . 3))
 (132 6 (:REWRITE FLOOR-=-X/Y . 2))
 (131 131 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (118 10 (:REWRITE |(floor x 2)| . 2))
 (110 10 (:REWRITE DEFAULT-FLOOR-RATIO))
 (109 32 (:REWRITE DEFAULT-PLUS-2))
 (106 10 (:REWRITE |(floor x 2)| . 1))
 (105 105
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (105 105
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (105 105 (:REWRITE |(< (/ x) 0)|))
 (105 105 (:REWRITE |(< (* x y) 0)|))
 (104 104 (:REWRITE DEFAULT-TIMES-2))
 (104 104 (:REWRITE DEFAULT-TIMES-1))
 (103 103
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (103 103
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (103 103
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (103 103 (:REWRITE |(equal c (/ x))|))
 (103 103 (:REWRITE |(equal c (- x))|))
 (103 103 (:REWRITE |(equal (/ x) c)|))
 (103 103 (:REWRITE |(equal (/ x) (/ y))|))
 (103 103 (:REWRITE |(equal (- x) c)|))
 (103 103 (:REWRITE |(equal (- x) (- y))|))
 (102 12 (:REWRITE |(* (- x) y)|))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (84 84 (:REWRITE REDUCE-RATIONALP-+))
 (84 84 (:REWRITE REDUCE-RATIONALP-*))
 (84 84 (:REWRITE RATIONALP-MINUS-X))
 (84 84 (:META META-RATIONALP-CORRECT))
 (81 1
     (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 1))
 (81 1
     (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
 (80 5 (:REWRITE |(+ x (if a b c))|))
 (64 64
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (60 12 (:REWRITE DEFAULT-MINUS))
 (54 12 (:REWRITE |(- (* c x))|))
 (38 1 (:LINEAR EXPT-<=-1-TWO))
 (37 1 (:LINEAR EXPT->-1-ONE))
 (33 1 (:LINEAR EXPT-X->=-X))
 (33 1 (:LINEAR EXPT-X->-X))
 (32 32 (:REWRITE DEFAULT-PLUS-1))
 (30 6 (:REWRITE FLOOR-ZERO . 5))
 (30 6 (:REWRITE FLOOR-ZERO . 2))
 (30 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (30 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (30 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (30 6
     (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (30 6 (:REWRITE FLOOR-CANCEL-*-CONST))
 (30 6
     (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (28 14
     (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 27 (:REWRITE NORMALIZE-ADDENDS))
 (24 24
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (24 24 (:REWRITE M1::MEMBER-SUBSETP))
 (24 2
     (:TYPE-PRESCRIPTION M1::NATP-FAST-MAIN-CLOCK-LEMMA))
 (15 3 (:DEFINITION M1::NCODE))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
 (10 10 (:REWRITE DEFAULT-FLOOR-2))
 (10 10 (:REWRITE DEFAULT-FLOOR-1))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 1 (:DEFINITION LEN))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6
    (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE |(floor x (- y))| . 2))
 (6 6 (:REWRITE |(floor x (- y))| . 1))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(floor (- x) y)| . 2))
 (6 6 (:REWRITE |(floor (- x) y)| . 1))
 (6 6
    (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (6 6
    (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 2
    (:TYPE-PRESCRIPTION M1::POSITIVE-NATP-NNIL))
 (4 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2
    (:TYPE-PRESCRIPTION M1::FAST-MAIN-CLOCK))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:DEFINITION M1::STATE-NAMEP))
 (2 1 (:LINEAR EXPT-<-1-TWO))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NATP-FIND-K!
 (32514 43 (:DEFINITION M1::TM-TO-TM1))
 (23883 1462 (:REWRITE DEFAULT-CDR))
 (23131 271 (:REWRITE M1::CONSP-ASSOC))
 (21724 284
        (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
 (21354 291 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
 (15412 31 (:DEFINITION M1::MAX-WIDTH1))
 (11714 142 (:DEFINITION ALISTP))
 (8908 62 (:DEFINITION M1::LOG2))
 (8477 271 (:DEFINITION ASSOC-EQUAL))
 (5914 1066 (:REWRITE ACL2-NUMBERP-X))
 (5749 494
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5547 62 (:DEFINITION MAX))
 (2455 2455 (:REWRITE DEFAULT-CAR))
 (2325 31 (:REWRITE |(< x (if a b c))|))
 (2196 3 (:DEFINITION M1::TURING-MACHINEP))
 (2184 3 (:DEFINITION M1::TURING-4-TUPLE))
 (2170 62 (:REWRITE ZP-OPEN))
 (2010 42 (:DEFINITION MEMBER-EQUAL))
 (1895 405
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (1836 1560 (:REWRITE INTEGERP-MINUS-X))
 (1835 406 (:REWRITE RATIONALP-X))
 (1767 1767 (:TYPE-PRESCRIPTION M1::LOG2))
 (1548 1548 (:REWRITE REDUCE-INTEGERP-+))
 (1548 1548 (:META META-INTEGERP-CORRECT))
 (1461 1461
       (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
 (1284 9 (:DEFINITION M1::SYMP))
 (1262 62 (:REWRITE |(floor x 2)| . 1))
 (1102 815 (:REWRITE DEFAULT-LESS-THAN-2))
 (1083 31
       (:REWRITE M1::LOG2-IMPLIES-EXPT-UPPERBOUND))
 (1007 781
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1007 781
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1002 815 (:REWRITE DEFAULT-LESS-THAN-1))
 (936 781 (:REWRITE SIMPLIFY-SUMS-<))
 (930 6
      (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
 (912 6 (:DEFINITION M1::HALF-TAPE))
 (901 494
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (816 12 (:REWRITE FLOOR-ZERO . 3))
 (815 815 (:REWRITE THE-FLOOR-BELOW))
 (815 815 (:REWRITE THE-FLOOR-ABOVE))
 (796 784
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (796 784
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (781 781
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (781 781 (:REWRITE INTEGERP-<-CONSTANT))
 (781 781 (:REWRITE CONSTANT-<-INTEGERP))
 (781 781
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (781 781
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (781 781
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (781 781
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (781 781 (:REWRITE |(< c (- x))|))
 (781 781
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (781 781
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (781 781
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (781 781
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (781 781 (:REWRITE |(< (/ x) (/ y))|))
 (781 781 (:REWRITE |(< (- x) c)|))
 (781 781 (:REWRITE |(< (- x) (- y))|))
 (762 3 (:DEFINITION M1::OPERATIONP))
 (752 494 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (741 739 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (740 370
      (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
 (701 232 (:REWRITE DEFAULT-PLUS-2))
 (682 62 (:REWRITE DEFAULT-FLOOR-RATIO))
 (636 12 (:REWRITE CANCEL-FLOOR-+))
 (582 582 (:REWRITE |(< (* x y) 0)|))
 (579 579
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (579 579
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (579 579 (:REWRITE |(< (/ x) 0)|))
 (496 31 (:REWRITE |(+ x (if a b c))|))
 (494 494
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (494 494
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (494 494
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (494 494 (:REWRITE |(equal c (/ x))|))
 (494 494 (:REWRITE |(equal c (- x))|))
 (494 494 (:REWRITE |(equal (/ x) c)|))
 (494 494 (:REWRITE |(equal (/ x) (/ y))|))
 (494 494 (:REWRITE |(equal (- x) c)|))
 (494 494 (:REWRITE |(equal (- x) (- y))|))
 (477 3 (:DEFINITION TRUE-LISTP))
 (440 110 (:REWRITE |(* y x)|))
 (418 418 (:REWRITE DEFAULT-TIMES-2))
 (418 418 (:REWRITE DEFAULT-TIMES-1))
 (406 406 (:REWRITE REDUCE-RATIONALP-*))
 (406 406 (:REWRITE RATIONALP-MINUS-X))
 (405 405 (:META META-RATIONALP-CORRECT))
 (390 390
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (390 390
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (390 390
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (390 390
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (360 12 (:REWRITE FLOOR-ZERO . 4))
 (360 12 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (345 7
      (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 1))
 (296 296
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (278 62 (:REWRITE |(floor x 2)| . 2))
 (264 12 (:REWRITE FLOOR-=-X/Y . 3))
 (264 12 (:REWRITE FLOOR-=-X/Y . 2))
 (232 232 (:REWRITE DEFAULT-PLUS-1))
 (204 24 (:REWRITE |(* (- x) y)|))
 (187 187
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (187 187 (:REWRITE NORMALIZE-ADDENDS))
 (180 180
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (180 180
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (180 180
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (180 180
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (166 4
      (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
 (120 24 (:REWRITE DEFAULT-MINUS))
 (108 24 (:REWRITE |(- (* c x))|))
 (76 2 (:LINEAR EXPT-<=-1-TWO))
 (74 2 (:LINEAR EXPT->-1-ONE))
 (72 72
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (72 72 (:REWRITE M1::MEMBER-SUBSETP))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (66 66 (:REWRITE |(< 0 (/ x))|))
 (66 66 (:REWRITE |(< 0 (* x y))|))
 (66 2 (:LINEAR EXPT-X->=-X))
 (66 2 (:LINEAR EXPT-X->-X))
 (62 62 (:REWRITE DEFAULT-FLOOR-2))
 (62 62 (:REWRITE DEFAULT-FLOOR-1))
 (62 62 (:REWRITE |(< y (+ (- c) x))|))
 (62 62 (:REWRITE |(< x (+ c/d y))|))
 (60 12 (:REWRITE FLOOR-ZERO . 5))
 (60 12 (:REWRITE FLOOR-ZERO . 2))
 (60 12 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (60 12 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (60 12 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (60 12
     (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (60 12 (:REWRITE FLOOR-CANCEL-*-CONST))
 (60 12
     (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (45 9 (:DEFINITION M1::NCODE))
 (30 30 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
 (24 24 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (24 24 (:TYPE-PRESCRIPTION ABS))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (21 3 (:DEFINITION LEN))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (12 12
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE |(floor x (- y))| . 2))
 (12 12 (:REWRITE |(floor x (- y))| . 1))
 (12 12
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (12 12
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (12 12 (:REWRITE |(floor (- x) y)| . 2))
 (12 12 (:REWRITE |(floor (- x) y)| . 1))
 (12 12
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (12 12
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (12 12
     (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:DEFINITION M1::STATE-NAMEP))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2
    (:REWRITE M1::POSITIVE-NATP-NCODE-REWRITE-VERSION))
 (4 2
    (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
 (4 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:TYPE-PRESCRIPTION M1::NATP-FIND-K!))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::M1-SIMULATION-OF-ROGERS-TM-TAKES-A-LONG-TIME
 (160 160 (:LINEAR M1::K-NON-0))
 (12
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))