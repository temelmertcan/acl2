(TEST-CONVERSION-TO-ARRAY
 (11 3 (:REWRITE BVCHOP-IDENTITY))
 (9 9 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (9 9 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (3 3 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (3 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (3 3 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (3 3 (:REWRITE BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES))
 (2 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (2 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-BV-ARRAY-WRITE-GEN-2))
 )
