(GL::G-IF-FN
 (3 3 (:TYPE-PRESCRIPTION MK-G-ITE))
 (2 1 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 )
(GL::G-IF-FN-PRESERVES-HYP
 (18 18 (:TYPE-PRESCRIPTION GL::BFR-HYP-FIX))
 (4 2 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::G-IF-FN-OF-BFR-HYP-FIX)
(GL::BFR-HYP-EQUIV-IMPLIES-EQUAL-G-IF-FN-4)
(GL::G-IF-FN-CORRECT
 (88 44 (:REWRITE GL::BFR-EVAL-BOOLEANP))
 (74 26 (:REWRITE DEFAULT-CAR))
 (50 50 (:TYPE-PRESCRIPTION BOOLEANP))
 (48 48 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:TYPE-PRESCRIPTION MK-G-ITE))
 (4 2 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 (2 2 (:REWRITE GL::BFR-ASSUME-FALSE))
 (2 1 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (1 1 (:TYPE-PRESCRIPTION GL::HYP$AP))
 )
(GL::GOBJ-DEPENDS-ON-OF-G-IF-FN
 (1443 13 (:DEFINITION GL::GOBJ-DEPENDS-ON))
 (234 78 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (189 189 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-VAR))
 (189 189 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-CONCRETE))
 (169 169 (:TYPE-PRESCRIPTION BOOLEANP))
 (91 13 (:REWRITE GL::GOBJ-LIST-DEPENDS-ON-OF-G-APPLY->ARGS))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->THEN))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->TEST))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->ELSE))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-INTEGER->BITS))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-BOOLEAN->BOOL))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-CDR-OF-GOBJ))
 (91 13 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ))
 (78 78 (:REWRITE GL::TAG-WHEN-ATOM))
 (65 13 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ-LIST))
 (39 39 (:TYPE-PRESCRIPTION GL::GOBJ-LIST-DEPENDS-ON))
 (26 26 (:REWRITE GL::GOBJ-LIST-DEPENDS-ON-OF-ATOM))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (26 13 (:REWRITE GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP))
 (13 13 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE GL::BFR-ASSUME-CORRECT))
 (3 3 (:TYPE-PRESCRIPTION MK-G-ITE))
 (2 1 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 (2 1 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (1 1 (:TYPE-PRESCRIPTION GL::HYP$AP))
 )
(GL::G-OR-FN
 (3 3 (:TYPE-PRESCRIPTION MK-G-ITE))
 (2 1 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 )
(GL::G-OR-FN-PRESERVES-HYP
 (18 18 (:TYPE-PRESCRIPTION GL::BFR-HYP-FIX))
 (6 3 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (3 3 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::G-OR-FN-OF-BFR-HYP-FIX)
(GL::BFR-HYP-EQUIV-IMPLIES-EQUAL-G-OR-FN-3)
(GL::G-OR-FN-CORRECT
 (50 42 (:REWRITE GL::GENERIC-GEVAL-NON-CONS))
 (46 23 (:REWRITE GL::BFR-EVAL-BOOLEANP))
 (44 16 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (25 25 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:TYPE-PRESCRIPTION MK-G-ITE))
 (4 2 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 (4 2 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (2 2 (:REWRITE GL::BFR-ASSUME-FALSE))
 )
(GL::GOBJ-DEPENDS-ON-OF-G-OR-FN
 (777 7 (:DEFINITION GL::GOBJ-DEPENDS-ON))
 (126 42 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (108 104 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-ATOM))
 (104 104 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-VAR))
 (104 104 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-CONCRETE))
 (91 91 (:TYPE-PRESCRIPTION BOOLEANP))
 (49 7 (:REWRITE GL::GOBJ-LIST-DEPENDS-ON-OF-G-APPLY->ARGS))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->THEN))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->TEST))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->ELSE))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-INTEGER->BITS))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-BOOLEAN->BOOL))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-CDR-OF-GOBJ))
 (49 7 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ))
 (42 42 (:REWRITE GL::TAG-WHEN-ATOM))
 (35 7 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ-LIST))
 (21 21 (:TYPE-PRESCRIPTION GL::GOBJ-LIST-DEPENDS-ON))
 (14 14 (:REWRITE GL::GOBJ-LIST-DEPENDS-ON-OF-ATOM))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (14 7 (:REWRITE GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE GL::BFR-ASSUME-CORRECT))
 (4 2 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (3 3 (:TYPE-PRESCRIPTION MK-G-ITE))
 (2 2 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (2 1 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 )
(GL::BODY-REPLACE-G-IFS)
