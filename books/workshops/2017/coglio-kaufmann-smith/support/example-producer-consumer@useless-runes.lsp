(PAIR-WITH-ALL)
(ALL-PAIRS)
(GOOD-PAIR-P)
(KEEP-GOOD-PAIRS)
(F)
(ALL-GOOD-PAIRS)
(RULE1
 (202 4 (:DEFINITION KEEP-GOOD-PAIRS))
 (116 32 (:REWRITE DEFAULT-CDR))
 (112 112 (:TYPE-PRESCRIPTION PAIR-WITH-ALL))
 (56 38 (:REWRITE DEFAULT-CAR))
 (53 53 (:TYPE-PRESCRIPTION ALL-PAIRS))
 (48 9 (:REWRITE CONSP-OF-APPEND))
 (48 8 (:DEFINITION BINARY-APPEND))
 (48 6 (:REWRITE CAR-OF-APPEND))
 (45 15 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (40 16 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (24 8 (:DEFINITION PAIR-WITH-ALL))
 (24 6 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 (15 15 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(KEEP-GOOD-PAIRS-OF-APPEND
 (132 42 (:REWRITE DEFAULT-CDR))
 (72 63 (:REWRITE DEFAULT-CAR))
 (37 37 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 12 (:REWRITE CAR-OF-APPEND))
 (18 18 (:REWRITE CONSP-OF-APPEND))
 (12 12 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 )
(ALL-GOOD-PAIRS$NOT-NORMALIZED)
(ALL-GOOD-PAIRS{1})
(ALL-GOOD-PAIRS-BEFORE-VS-AFTER-0)
(ALL-GOOD-PAIRS{1}-COPY)
(ALL-GOOD-PAIRS{1}-COPY-DEF)
(ALL-GOOD-PAIRS{1}-IS-ALL-GOOD-PAIRS{1}-COPY)
(ALL-GOOD-PAIRS-BECOMES-ALL-GOOD-PAIRS{1}-LEMMA)
(ALL-GOOD-PAIRS-BECOMES-ALL-GOOD-PAIRS{1})
(PAIR-WITH-ALL-AND-FILTER)
(RULE2
 (27 24 (:REWRITE DEFAULT-CAR))
 (18 16 (:REWRITE DEFAULT-CDR))
 )
(ALL-GOOD-PAIRS{1}$NOT-NORMALIZED)
(ALL-GOOD-PAIRS{2})
(ALL-GOOD-PAIRS{1}-BEFORE-VS-AFTER-0)
(ALL-GOOD-PAIRS{2}-COPY)
(ALL-GOOD-PAIRS{2}-COPY-DEF)
(ALL-GOOD-PAIRS{2}-IS-ALL-GOOD-PAIRS{2}-COPY)
(ALL-GOOD-PAIRS{1}-BECOMES-ALL-GOOD-PAIRS{2}-LEMMA)
(ALL-GOOD-PAIRS{1}-BECOMES-ALL-GOOD-PAIRS{2})
(F$NOT-NORMALIZED)
(F-FAST)
(F-BEFORE-VS-AFTER-0)
(F-FAST-COPY)
(F-FAST-COPY-DEF)
(F-FAST-IS-F-FAST-COPY)
(F-BECOMES-F-FAST-LEMMA)
(F-BECOMES-F-FAST)
