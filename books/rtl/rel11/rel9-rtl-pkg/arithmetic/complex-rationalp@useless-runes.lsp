(RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-RATIONAL
 (2 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 )
(RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-NOT-COMPLEX
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-RATIONAL))
 )
(RTL::COMPLEX-RATIONALP-+-WHEN-FIRST-TERM-IS-RATIONAL
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-RATIONAL))
 (1 1 (:REWRITE RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-NOT-COMPLEX))
 )
(RTL::COMPLEX-RATIONALP-+-WHEN-FIRST-TERM-IS-NOT-COMPLEX
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-RATIONAL))
 (1 1 (:REWRITE RTL::COMPLEX-RATIONALP-+-WHEN-SECOND-TERM-IS-NOT-COMPLEX))
 (1 1 (:REWRITE RTL::COMPLEX-RATIONALP-+-WHEN-FIRST-TERM-IS-RATIONAL))
 )
(RTL::COMPLEX-RATIONALP-*-DROP-FIRST-TERM-IF-RATIONAL
 (3 2 (:REWRITE DEFAULT-*-2))
 (3 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
