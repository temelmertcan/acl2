(PADDING::PAD-TO-896-NUMBER-OF-ZEROS-CORRECT
     (2349 246 (:REWRITE MOD-WHEN-MULTIPLE))
     (2349 246
           (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (1880 492 (:REWRITE COMMUTATIVITY-OF-*))
     (1342 436
           (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (1066 1066 (:REWRITE DEFAULT-*-2))
     (1066 1066 (:REWRITE DEFAULT-*-1))
     (979 319 (:REWRITE DEFAULT-+-2))
     (538 319 (:REWRITE DEFAULT-+-1))
     (413 230 (:REWRITE DEFAULT-<-1))
     (404 68 (:REWRITE DISTRIBUTIVITY))
     (328 328
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (290 230 (:REWRITE DEFAULT-<-2))
     (216 216
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (216 216
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (216 216
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (216 216
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (44 44 (:REWRITE DEFAULT-UNARY-MINUS)))
