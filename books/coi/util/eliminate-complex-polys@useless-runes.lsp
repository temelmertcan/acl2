(PESUDO-COMPLEX-RATIONALP)
(COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP)
(PESUDO-COMPLEX-RATIONALP-COMPLEX)
(PESUDO-COMPLEX-RATIONALP-+)
(PESUDO-COMPLEX-RATIONALP-*)
(PESUDO-COMPLEX-RATIONALP--)
(PESUDO-COMPLEX-RATIONALP-/)
(PESUDO-COMPLEX-RATIONALP-REALPART-IMAGPART
 (1 1
    (:TYPE-PRESCRIPTION COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP)))
(REALPART-RATIONALP
 (24 24
     (:TYPE-PRESCRIPTION COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP))
 (2 2 (:REWRITE DEFAULT-REALPART)))
(IMAGPART-RATIONALP)
(REALPART-COMPLEX-BETTER (3 3 (:REWRITE DEFAULT-REALPART)))
(IMAGPART-COMPLEX-BETTER (5 5 (:REWRITE DEFAULT-COMPLEX-2))
                         (4 4 (:REWRITE IMAGPART-RATIONALP))
                         (4 4 (:REWRITE DEFAULT-IMAGPART)))
(REALPART-* (6 6
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (6 5 (:REWRITE DEFAULT-*-2))
            (6 5 (:REWRITE DEFAULT-*-1))
            (6 4 (:REWRITE DEFAULT-REALPART))
            (6 4 (:REWRITE DEFAULT-IMAGPART))
            (4 4 (:REWRITE REALPART-RATIONALP))
            (4 4 (:REWRITE IMAGPART-RATIONALP))
            (4 4 (:REWRITE DEFAULT-+-2))
            (4 4 (:REWRITE DEFAULT-+-1))
            (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(IMAGPART-* (8 7 (:REWRITE DEFAULT-*-2))
            (8 7 (:REWRITE DEFAULT-*-1))
            (6 6
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (6 4 (:REWRITE DEFAULT-REALPART))
            (6 4 (:REWRITE DEFAULT-IMAGPART))
            (4 4 (:REWRITE REALPART-RATIONALP))
            (4 4 (:REWRITE IMAGPART-RATIONALP))
            (4 4 (:REWRITE DEFAULT-+-2))
            (4 4 (:REWRITE DEFAULT-+-1)))
(NEGATE-TO-TIMES)
(REALPART-- (6 5 (:REWRITE DEFAULT-*-2))
            (5 5 (:REWRITE DEFAULT-*-1))
            (3 3
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (3 2 (:REWRITE DEFAULT-REALPART))
            (2 2 (:REWRITE REALPART-RATIONALP))
            (2 1 (:REWRITE DEFAULT-IMAGPART))
            (1 1 (:REWRITE IMAGPART-RATIONALP))
            (1 1 (:REWRITE DEFAULT-+-2))
            (1 1 (:REWRITE DEFAULT-+-1)))
(IMAGPART-- (5 4 (:REWRITE DEFAULT-*-2))
            (4 4 (:REWRITE DEFAULT-*-1))
            (3 3
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (3 2 (:REWRITE DEFAULT-IMAGPART))
            (2 2 (:REWRITE IMAGPART-RATIONALP))
            (2 2 (:REWRITE DEFAULT-+-2))
            (2 2 (:REWRITE DEFAULT-+-1))
            (2 1 (:REWRITE DEFAULT-REALPART))
            (1 1 (:REWRITE REALPART-RATIONALP)))
(STRONG-EQUAL-ACL2-NUMBERP
 (182
     182
     (:TYPE-PRESCRIPTION COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP))
 (22 22 (:REWRITE REALPART-RATIONALP))
 (22 22 (:REWRITE IMAGPART-RATIONALP))
 (22 22 (:REWRITE DEFAULT-REALPART))
 (22 22 (:REWRITE DEFAULT-IMAGPART))
 (13 13
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-COMPLEX-2))
 (4 4 (:REWRITE DEFAULT-COMPLEX-1)))
(NON-ZERO-IMAGPART)
(NON-NEGATIVE-PRODUCT)
(POSITIVE-PRODUCT)
(POSITIVE-EXPT (3 3 (:REWRITE DEFAULT-*-2))
               (3 3 (:REWRITE DEFAULT-*-1))
               (2 1 (:REWRITE DEFAULT-<-2))
               (1 1 (:REWRITE DEFAULT-<-1)))
(NON-NEGATIVE-EXPT
     (24 24
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (3 3 (:REWRITE DEFAULT-*-2))
     (3 3 (:REWRITE DEFAULT-*-1))
     (2 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:LINEAR POSITIVE-EXPT)))
(DEFINITION-OF-INVERSE
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (16 4 (:REWRITE RATIONALP-X))
     (14 1 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE DEFAULT-DIVIDE)))
(COMPLEX-RECIPORICAL
 (208 208
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (208 208
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (208 208
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (170 86 (:REWRITE DEFAULT-TIMES-2))
 (155 155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (155
  155
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (155 155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (155 155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (155
     155
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (155 155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (155 155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (155 155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (114 1 (:REWRITE |(equal x (/ y))|))
 (110 1 (:REWRITE |(not (equal x (/ y)))|))
 (105 86 (:REWRITE DEFAULT-TIMES-1))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (87 35 (:REWRITE DEFAULT-PLUS-2))
 (81 35 (:REWRITE DEFAULT-PLUS-1))
 (62 2 (:LINEAR EXPT-<=-1-ONE))
 (60 2 (:LINEAR EXPT->=-1-TWO))
 (60 2 (:LINEAR EXPT->-1-TWO))
 (60 2 (:LINEAR EXPT-<-1-ONE))
 (54 2 (:LINEAR EXPT-X->=-X))
 (54 2 (:LINEAR EXPT->=-1-ONE))
 (54 2 (:LINEAR EXPT-<=-1-TWO))
 (52 2 (:LINEAR EXPT-X->-X))
 (52 2 (:LINEAR EXPT->-1-ONE))
 (52 2 (:LINEAR EXPT-<-1-TWO))
 (50 2 (:REWRITE |(* (* x y) z)|))
 (43 19 (:REWRITE DEFAULT-MINUS))
 (34 34 (:REWRITE DEFAULT-EXPT-2))
 (34 34 (:REWRITE DEFAULT-EXPT-1))
 (34 34 (:REWRITE |(expt 1/c n)|))
 (34 34 (:REWRITE |(expt (- x) n)|))
 (31 31 (:REWRITE DEFAULT-REALPART))
 (31 31 (:REWRITE DEFAULT-IMAGPART))
 (28 2 (:LINEAR POSITIVE-PRODUCT))
 (21 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20 (:REWRITE SIMPLIFY-SUMS-<))
 (20 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (20 20 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (19 2 (:LINEAR POSITIVE-EXPT))
 (18 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (18 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (17 17
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (17 17 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE DEFAULT-COMPLEX-2))
 (13 13 (:REWRITE DEFAULT-COMPLEX-1))
 (12 12 (:REWRITE |(* c (* d x))|))
 (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(REALPART-/ (28 7 (:REWRITE DEFAULT-UNARY-/))
            (25 17 (:REWRITE DEFAULT-*-2))
            (17 17 (:REWRITE DEFAULT-*-1))
            (14 7 (:REWRITE DEFAULT-+-2))
            (14 7 (:REWRITE DEFAULT-+-1))
            (10 10 (:REWRITE DEFAULT-REALPART))
            (7 7 (:REWRITE DEFAULT-IMAGPART))
            (7 4 (:LINEAR POSITIVE-PRODUCT))
            (6 6
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
            (1 1 (:REWRITE RATIONALP-UNARY-/))
            (1 1 (:REWRITE DEFAULT-COMPLEX-2))
            (1 1 (:REWRITE DEFAULT-COMPLEX-1)))
(IMAGPART-/ (25 17 (:REWRITE DEFAULT-*-2))
            (24 5 (:REWRITE DEFAULT-UNARY-/))
            (17 17 (:REWRITE DEFAULT-*-1))
            (13 6 (:REWRITE DEFAULT-+-2))
            (11 6 (:REWRITE DEFAULT-+-1))
            (10 10 (:REWRITE DEFAULT-IMAGPART))
            (7 7 (:REWRITE REALPART-RATIONALP))
            (7 7 (:REWRITE DEFAULT-REALPART))
            (7 4 (:LINEAR POSITIVE-PRODUCT))
            (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
            (2 2
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (1 1 (:REWRITE RATIONALP-UNARY-/))
            (1 1 (:REWRITE DEFAULT-COMPLEX-2))
            (1 1 (:REWRITE DEFAULT-COMPLEX-1)))
(<-PESUDO-COMPLEX-RATIONALP
 (232
     232
     (:TYPE-PRESCRIPTION COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP))
 (24 24
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4
    (:REWRITE COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP)))
(EQUAL-PESUDO-COMPLEX-RATIONALP
 (196
     196
     (:TYPE-PRESCRIPTION COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP))
 (22 22 (:REWRITE REALPART-RATIONALP))
 (22 22 (:REWRITE IMAGPART-RATIONALP))
 (22 22 (:REWRITE DEFAULT-REALPART))
 (22 22 (:REWRITE DEFAULT-IMAGPART))
 (13 13
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-COMPLEX-2))
 (4 4 (:REWRITE DEFAULT-COMPLEX-1))
 (1 1
    (:REWRITE COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP)))
(COMPLEX-POLY-TEST
     (616 11
          (:REWRITE EQUAL-PESUDO-COMPLEX-RATIONALP))
     (481 481
          (:REWRITE COMPLEX-RATIONALP-IMPLIES-PESUDO-COMPLEX-RATIONALP))
     (137 137 (:REWRITE DEFAULT-+-2))
     (137 137 (:REWRITE DEFAULT-+-1))
     (114 64 (:REWRITE DEFAULT-REALPART))
     (110 110
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (99 53 (:REWRITE DEFAULT-IMAGPART))
     (92 64 (:REWRITE REALPART-RATIONALP))
     (90 84 (:REWRITE DEFAULT-*-2))
     (84 84 (:REWRITE DEFAULT-*-1))
     (81 81 (:REWRITE FOLD-CONSTS-IN-+))
     (67 53 (:REWRITE IMAGPART-RATIONALP))
     (56 48 (:REWRITE DEFAULT-UNARY-MINUS))
     (42 21 (:REWRITE RATIONALP-+))
     (26 26 (:REWRITE DEFAULT-<-2))
     (26 26 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE RATIONALP-UNARY--))
     (9 9 (:REWRITE RATIONALP-*)))