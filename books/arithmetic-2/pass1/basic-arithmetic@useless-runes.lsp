(FUNCTIONAL-SELF-INVERSION-OF-MINUS
 (3 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(MINUS-CANCELLATION-ON-RIGHT
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(MINUS-CANCELLATION-ON-LEFT
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 3 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(RIGHT-CANCELLATION-FOR-+
 (23 23 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 10 (:REWRITE DEFAULT-+-2))
 )
(LEFT-CANCELLATION-FOR-+
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 8 (:REWRITE DEFAULT-+-1))
 )
(EQUAL-MINUS-0
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(EQUAL-+-X-Y-0
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(EQUAL-+-X-Y-X
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-+-1))
 )
(EQUAL-+-X-Y-Y
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 )
(EQUAL-MINUS-MINUS
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(/-CANCELLATION-ON-RIGHT
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 6 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE DEFAULT-*-2))
 (5 2 (:REWRITE DEFAULT-UNARY-/))
 )
(/-CANCELLATION-ON-LEFT
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 1 (:REWRITE DEFAULT-UNARY-/))
 (3 2 (:REWRITE DEFAULT-*-2))
 (3 2 (:REWRITE DEFAULT-*-1))
 )
(LEFT-CANCELLATION-FOR-*
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 4 (:REWRITE DEFAULT-*-2))
 (7 4 (:REWRITE DEFAULT-*-1))
 )
(EQUAL-/-0
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 1 (:REWRITE DEFAULT-UNARY-/))
 (3 2 (:REWRITE DEFAULT-*-2))
 (3 2 (:REWRITE DEFAULT-*-1))
 )
(EQUAL-*-X-Y-0
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-*-2))
 (2 1 (:REWRITE DEFAULT-*-1))
 )
(EQUAL-*-X-Y-X
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 )
(EQUAL-*-Y-X-X
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 )
(FOLD-CONSTS-IN-*)
(NUMERATOR-NONZERO-FORWARD
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 )
(TIMES-ZERO)
(FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
 (6 4 (:REWRITE DEFAULT-*-2))
 (6 4 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(RECIPROCAL-MINUS-A
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 3 (:REWRITE DEFAULT-UNARY-/))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 )
