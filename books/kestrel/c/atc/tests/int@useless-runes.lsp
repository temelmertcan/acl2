(|f|
 (534 534 (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (462 462 (:REWRITE |arith (* c (* d x))|))
 (210 60 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (196 196 (:REWRITE |arith (* (- x) y)|))
 (184 184 (:REWRITE |arith (- (* c x))|))
 (182 51 (:REWRITE DEFAULT-PLUS-2))
 (144 60 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (140 62 (:REWRITE DEFAULT-LESS-THAN-2))
 (140 62 (:REWRITE DEFAULT-LESS-THAN-1))
 (132 56 (:REWRITE SIMPLIFY-SUMS-<))
 (114 51 (:REWRITE DEFAULT-PLUS-1))
 (63 32 (:REWRITE DEFAULT-TIMES-2))
 (62 62 (:REWRITE THE-FLOOR-BELOW))
 (62 62 (:REWRITE THE-FLOOR-ABOVE))
 (62 62 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (62 62 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (62 62 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (60 60 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (60 60 (:REWRITE INTEGERP-<-CONSTANT))
 (60 60 (:REWRITE CONSTANT-<-INTEGERP))
 (60 60 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (60 60 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (60 60 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (60 60 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< c (- x))|))
 (60 60 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (60 60 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (60 60 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (60 60 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< (/ x) (/ y))|))
 (60 60 (:REWRITE |(< (- x) c)|))
 (60 60 (:REWRITE |(< (- x) (- y))|))
 (51 32 (:REWRITE DEFAULT-TIMES-1))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (29 29 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (23 23 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (2 2 (:REWRITE |arith (+ c (+ d x))|))
 (2 2 (:REWRITE |(* x (- y))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 )
(C::*PROGRAM*-WELL-FORMED)
(|f-RETURNS-VALUE|)
(|f-EXEC-CONST-LIMIT-CORRECT|
 (2136 1 (:REWRITE C::EXEC-BLOCK-ITEM-LIST-UNROLL))
 (330 330 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (112 100 (:REWRITE C::NOT-SINTP-WHEN-UCHARP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-UINTP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
 (100 100 (:REWRITE C::NOT-SINTP-WHEN-POINTERP))
 (64 64 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (64 64 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (64 64 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (64 64 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (64 64 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (64 64 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (64 64 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (64 64 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (64 64 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (64 64 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (36 36 (:REWRITE C::NOT-ERRORP-WHEN-VALUE-LISTP))
 (36 36 (:REWRITE C::NOT-ERRORP-WHEN-UCHAR-ARRAYP))
 (36 36 (:REWRITE C::NOT-ERRORP-WHEN-SCOPE-LISTP))
 (35 35 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-5))
 (34 34 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (34 34 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (34 34 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (34 34 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (34 34 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (34 34 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (34 34 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (34 34 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (34 34 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (34 34 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (30 30 (:REWRITE C::NOT-SLONGP-WHEN-ULONGP))
 (30 30 (:REWRITE C::NOT-SLONGP-WHEN-ULLONGP))
 (30 30 (:REWRITE C::NOT-SLONGP-WHEN-SLLONGP))
 (30 30 (:REWRITE C::NOT-SLONGP-WHEN-POINTERP))
 (30 30 (:REWRITE C::NOT-SLLONGP-WHEN-ULONGP))
 (30 30 (:REWRITE C::NOT-SLLONGP-WHEN-ULLONGP))
 (30 30 (:REWRITE C::NOT-SLLONGP-WHEN-SLONGP))
 (30 30 (:REWRITE C::NOT-SLLONGP-WHEN-POINTERP))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-3))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-2))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-1))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-BASE-8))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-BASE-7))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-BASE-6))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-BASE-5))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-BASE-4))
 (20 20 (:REWRITE C::EXEC-EXPR-PURE-BASE-3))
 (19 19 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (19 19 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (19 19 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (19 19 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (19 19 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (6 6 (:REWRITE C::EXEC-STMT-UNROLL-2))
 (6 6 (:REWRITE C::EXEC-STMT-UNROLL-1))
 (3 3 (:REWRITE C::VALUEP-WHEN-UCHARP))
 (2 1 (:REWRITE C::INIT-SCOPE-BASE-2))
 (1 1 (:REWRITE C::EXEC-STMT-BASE-8))
 (1 1 (:REWRITE C::EXEC-STMT-BASE-7))
 (1 1 (:REWRITE C::EXEC-STMT-BASE-6))
 (1 1 (:REWRITE C::EXEC-STMT-BASE-5))
 (1 1 (:REWRITE C::EXEC-STMT-BASE-4))
 )
(|f-EXEC-VAR-LIMIT-CORRECT|)
(C::|*PROGRAM*-f-CORRECT|)
