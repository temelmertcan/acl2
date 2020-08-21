(BITOPS::FAST-LOGEXT-EXEC$INLINE
     (13 7
         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-1))
     (5 5
        (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-2))
     (5 5
        (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-1)))
(BITOPS::L0 (6 3
               (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
            (6 3
               (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
            (3 3 (:TYPE-PRESCRIPTION NEGP))
            (3 3 (:TYPE-PRESCRIPTION NATP))
            (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
            (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(BITOPS::L1 (15 3 (:LINEAR BITOPS::LOGCAR-BOUND))
            (13 5 (:REWRITE BITOPS::LOGCAR-OF-BIT))
            (8 8 (:TYPE-PRESCRIPTION BITP))
            (6 6 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
            (6 3 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
            (6 3 (:REWRITE BFIX-WHEN-BIT->BOOL))
            (4 2 (:REWRITE BFIX-WHEN-NOT-BITP))
            (2 1 (:REWRITE DEFAULT-+-2))
            (2 1 (:REWRITE DEFAULT-+-1))
            (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(BITOPS::L2 (10 4 (:REWRITE BITOPS::LOGCAR-OF-BIT))
            (10 2 (:LINEAR BITOPS::LOGCAR-BOUND))
            (7 5 (:REWRITE DEFAULT-+-2))
            (7 5 (:REWRITE DEFAULT-+-1))
            (6 6 (:TYPE-PRESCRIPTION BITP))
            (2 2
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(BITOPS::FAST-LOGEXT-EXEC-IS-LOGEXT
     (4239 23 (:REWRITE LOGEXT-IDENTITY))
     (4170 53
           (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGCDR))
     (4060 15
           (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (3170 23 (:DEFINITION SIGNED-BYTE-P))
     (2922 14 (:REWRITE BITOPS::LOGCDR-OF-LOGAND))
     (2183 252 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
     (1923 820 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (1859 23 (:DEFINITION INTEGER-RANGE-P))
     (1858 47 (:DEFINITION BITOPS::LOGNOT$))
     (1766 655 (:REWRITE DEFAULT-+-2))
     (1058 529
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
     (1050 350 (:REWRITE <-0-+-NEGATIVE-1))
     (958 17
          (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
     (921 17
          (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
     (893 655 (:REWRITE DEFAULT-+-1))
     (868 868 (:TYPE-PRESCRIPTION BITP))
     (833 603 (:REWRITE DEFAULT-<-2))
     (792 792
          (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
     (731 603 (:REWRITE DEFAULT-<-1))
     (712 14 (:REWRITE BITOPS::LOGCAR-OF-LOGAND))
     (552 23 (:DEFINITION SIGNED-BYTE-P**))
     (529 529
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
     (529 529
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (520 462
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (304 23 (:LINEAR EXPT->-1))
     (304 14 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
     (228 228 (:REWRITE ASH-0))
     (195 15
          (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (195 15
          (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (154 77 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (154 77 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (151 151 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (141 71 (:REWRITE BFIX-WHEN-NOT-BITP))
     (128 13 (:REWRITE NATP-POSP))
     (122 122 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (117 117
          (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (64 64
         (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (48 16 (:REWRITE ZP-WHEN-GT-0))
     (46 46
         (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
     (46 46 (:REWRITE EXPONENTS-ADD))
     (46 46
         (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
     (30 30 (:REWRITE BITOPS::ASH-<-0))
     (24 12 (:REWRITE POSP-NATP))
     (16 16 (:REWRITE ZP-WHEN-INTEGERP))
     (16 16 (:REWRITE ZP-OPEN))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (1 1 (:REWRITE POSP-RW))
     (1 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE NATP-RW)))
(FAST-LOGEXT-FN
     (38 2 (:REWRITE LOGEXT-IDENTITY))
     (33 1 (:DEFINITION SIGNED-BYTE-P))
     (27 1 (:DEFINITION INTEGER-RANGE-P))
     (12 12
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (12 12
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (7 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (1 1
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (1 1 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(BITOPS::FAST-LOGEXT8-CRUX
     (140 4
          (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (126 14 (:REWRITE LOGHEAD-IDENTITY))
     (100 100
          (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (96 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
     (96 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
     (84 14 (:DEFINITION UNSIGNED-BYTE-P))
     (80 16 (:DEFINITION INTEGER-RANGE-P))
     (72 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
     (68 50 (:REWRITE DEFAULT-<-1))
     (50 50 (:REWRITE DEFAULT-<-2))
     (36 16 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (36 6 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (28 14
         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (24 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
     (20 2 (:REWRITE LOGEXT-IDENTITY))
     (18 6 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (14 14 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (14 14
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 6 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (9 3 (:REWRITE DEFAULT-+-2))
     (6 6 (:TYPE-PRESCRIPTION NEGP))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE NEGP-WHEN-INTEGERP))
     (6 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT8$INLINE
     (62 62
         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (12 4 (:REWRITE LOGHEAD-IDENTITY))
     (10 2 (:DEFINITION INTEGER-RANGE-P))
     (10 1 (:REWRITE LOGEXT-IDENTITY))
     (6 1 (:DEFINITION UNSIGNED-BYTE-P))
     (6 1 (:DEFINITION SIGNED-BYTE-P))
     (5 4
        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (1 1
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (1 1
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT16-CRUX
     (140 4
          (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (126 14 (:REWRITE LOGHEAD-IDENTITY))
     (100 100
          (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (96 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
     (96 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
     (84 14 (:DEFINITION UNSIGNED-BYTE-P))
     (80 16 (:DEFINITION INTEGER-RANGE-P))
     (72 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
     (68 50 (:REWRITE DEFAULT-<-1))
     (50 50 (:REWRITE DEFAULT-<-2))
     (36 16 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (36 6 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (28 14
         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (24 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
     (20 2 (:REWRITE LOGEXT-IDENTITY))
     (18 6 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (14 14 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (14 14
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 6 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (9 3 (:REWRITE DEFAULT-+-2))
     (6 6 (:TYPE-PRESCRIPTION NEGP))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE NEGP-WHEN-INTEGERP))
     (6 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT16$INLINE
     (62 62
         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (12 4 (:REWRITE LOGHEAD-IDENTITY))
     (10 2 (:DEFINITION INTEGER-RANGE-P))
     (10 1 (:REWRITE LOGEXT-IDENTITY))
     (6 1 (:DEFINITION UNSIGNED-BYTE-P))
     (6 1 (:DEFINITION SIGNED-BYTE-P))
     (5 4
        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (1 1
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (1 1
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT32-CRUX
     (140 4
          (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (126 14 (:REWRITE LOGHEAD-IDENTITY))
     (100 100
          (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (96 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
     (96 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
     (84 14 (:DEFINITION UNSIGNED-BYTE-P))
     (80 16 (:DEFINITION INTEGER-RANGE-P))
     (72 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
     (68 50 (:REWRITE DEFAULT-<-1))
     (50 50 (:REWRITE DEFAULT-<-2))
     (36 16 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (36 6 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (28 14
         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (24 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
     (20 2 (:REWRITE LOGEXT-IDENTITY))
     (18 6 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (14 14 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (14 14
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 6 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (9 3 (:REWRITE DEFAULT-+-2))
     (6 6 (:TYPE-PRESCRIPTION NEGP))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE NEGP-WHEN-INTEGERP))
     (6 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT32$INLINE
     (62 62
         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (12 4 (:REWRITE LOGHEAD-IDENTITY))
     (10 2 (:DEFINITION INTEGER-RANGE-P))
     (10 1 (:REWRITE LOGEXT-IDENTITY))
     (6 1 (:DEFINITION UNSIGNED-BYTE-P))
     (6 1 (:DEFINITION SIGNED-BYTE-P))
     (5 4
        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (1 1
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (1 1
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT64-CRUX
     (140 4
          (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (140 4 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (126 14 (:REWRITE LOGHEAD-IDENTITY))
     (100 100
          (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (96 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
     (96 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
     (84 14 (:DEFINITION UNSIGNED-BYTE-P))
     (80 16 (:DEFINITION INTEGER-RANGE-P))
     (72 6
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
     (68 50 (:REWRITE DEFAULT-<-1))
     (50 50 (:REWRITE DEFAULT-<-2))
     (36 16 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (36 6 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (28 14
         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (24 6
         (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
     (20 2 (:REWRITE LOGEXT-IDENTITY))
     (18 6 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (14 14 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (14 14
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 6 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (9 3 (:REWRITE DEFAULT-+-2))
     (6 6 (:TYPE-PRESCRIPTION NEGP))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE NEGP-WHEN-INTEGERP))
     (6 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::FAST-LOGEXT64$INLINE
     (62 62
         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (36 4 (:REWRITE LOGHEAD-IDENTITY))
     (29 29 (:REWRITE DEFAULT-<-2))
     (29 29 (:REWRITE DEFAULT-<-1))
     (24 4 (:DEFINITION UNSIGNED-BYTE-P))
     (8 4
        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (4 4
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (4 4
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (3 3
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(BITOPS::LOGEXT-OF-GREATER-THAN-LENGTH
     (468 11 (:REWRITE LOGEXT-IDENTITY))
     (330 8 (:DEFINITION SIGNED-BYTE-P))
     (281 7 (:DEFINITION INTEGER-RANGE-P))
     (222 4 (:DEFINITION SIGNED-BYTE-P**))
     (184 33 (:REWRITE ZIP-OPEN))
     (180 2
          (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGCDR))
     (138 48 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (130 56
          (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (128 128 (:TYPE-PRESCRIPTION BITP))
     (126 126 (:TYPE-PRESCRIPTION NATP))
     (94 58 (:REWRITE DEFAULT-<-2))
     (94 58 (:REWRITE DEFAULT-<-1))
     (87 19 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (84 84
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (84 84
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (74 35
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (74 35
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (74 35
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
     (64 42 (:REWRITE DEFAULT-+-2))
     (45 3
         (:REWRITE BITOPS::LOGEXT-OF-0-I-WHEN-LOGCAR-0))
     (42 42 (:REWRITE DEFAULT-+-1))
     (42 3
         (:REWRITE BITOPS::LOGEXT-OF-0-I-WHEN-LOGCAR-1))
     (40 3
         (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT))
     (29 25 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (28 28 (:REWRITE ZP-WHEN-INTEGERP))
     (28 28 (:REWRITE ZP-OPEN))
     (21 21 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (21 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (17 17
         (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (16 4 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12
         (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (12 12
         (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
     (11 1 (:REWRITE BFIX-WHEN-NOT-1))
     (4 4 (:REWRITE BITOPS::LOGCDR-<-CONST))
     (4 2 (:REWRITE UNICITY-OF-0))
     (3 3 (:REWRITE BITOPS::SIGNED-BYTE-P-0-X))
     (2 2 (:DEFINITION FIX))
     (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
     (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (2 1 (:REWRITE BFIX-WHEN-BITP))
     (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL)))
(BITOPS::BIGNUM-LOGEXT$INLINE
     (74 2 (:REWRITE LOGEXT-IDENTITY))
     (66 2 (:DEFINITION SIGNED-BYTE-P))
     (54 2 (:DEFINITION INTEGER-RANGE-P))
     (24 24
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (24 24
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (20 12 (:REWRITE DEFAULT-<-2))
     (17 12 (:REWRITE DEFAULT-<-1))
     (6 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(BITOPS::LOGHEAD-OF-GREATER-THAN-LENGTH
     (2362 1070
           (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (1655 13 (:REWRITE LOGHEAD-IDENTITY))
     (1167 14 (:DEFINITION UNSIGNED-BYTE-P**))
     (1108 25 (:DEFINITION UNSIGNED-BYTE-P))
     (1077 20 (:DEFINITION INTEGER-RANGE-P))
     (1048 70 (:REWRITE ZIP-OPEN))
     (991 991 (:TYPE-PRESCRIPTION NATP))
     (800 119 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (743 30 (:REWRITE UNSIGNED-BYTE-P-PLUS))
     (710 101 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (563 41 (:DEFINITION BIT->BOOL$INLINE))
     (506 506 (:TYPE-PRESCRIPTION BITP))
     (417 39
          (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (390 43 (:LINEAR BITOPS::LOGCAR-BOUND))
     (332 40 (:REWRITE BITOPS::LOGCDR-<-CONST))
     (293 135
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (270 135
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (240 10 (:REWRITE IFIX-EQUAL-TO-NONZERO))
     (214 214 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (187 125 (:REWRITE DEFAULT-<-2))
     (184 125 (:REWRITE DEFAULT-<-1))
     (143 143 (:TYPE-PRESCRIPTION POSP))
     (141 141
          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (112 112
          (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (109 75 (:REWRITE DEFAULT-+-2))
     (91 44 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (82 8
         (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT))
     (75 75 (:REWRITE DEFAULT-+-1))
     (71 71
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (71 71
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (49 49
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (33 3 (:REWRITE BFIX-WHEN-NOT-1))
     (24 4 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (23 23 (:REWRITE ZP-OPEN))
     (12 4 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (12 4 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (10 10
         (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
     (8 4 (:REWRITE NATP-WHEN-GTE-0))
     (6 3 (:REWRITE BFIX-WHEN-NOT-BITP))
     (6 3 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (6 3 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (4 4 (:TYPE-PRESCRIPTION NEGP))
     (4 4 (:REWRITE NEGP-WHEN-INTEGERP))
     (2 2 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:INDUCTION BITOPS::LOGBITP-INDUCT)))
(BITOPS::BIGNUM-LOGHEAD$INLINE
     (34 2 (:REWRITE LOGHEAD-IDENTITY))
     (29 18 (:REWRITE DEFAULT-<-1))
     (28 2 (:DEFINITION UNSIGNED-BYTE-P))
     (26 2 (:DEFINITION INTEGER-RANGE-P))
     (22 18 (:REWRITE DEFAULT-<-2))
     (15 5
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (15 5
         (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (10 10 (:TYPE-PRESCRIPTION BITP))
     (10 10 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (8 8
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (8 8
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (2 2
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))