(STD::DEFCONSTRAINED-RECOGNIZER-FN
 (10 10 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(STD::MAYBE-PSEUDO-EVENT-FORMP-OF-DEFCONSTRAINED-RECOGNIZER-FN
 (40 5 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (16 16 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 5 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (10 7 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (9 9 (:TYPE-PRESCRIPTION SYMBOLP-PKG-WITNESS))
 (8 8 (:REWRITE DEFAULT-SYMBOL-NAME))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (8 4 (:REWRITE DEFAULT-COERCE-3))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 3 (:REWRITE SYMBOL-PACKAGE-NAME-PKG-WITNESS-NAME))
 (6 3 (:REWRITE DEFAULT-PKG-IMPORTS))
 )
