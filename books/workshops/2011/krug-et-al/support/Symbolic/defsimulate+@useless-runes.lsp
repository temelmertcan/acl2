(SNOC)
(DELLAST)
(LASTVAL)
(PACKN+)
(DEFSIMULATE+-CORE)
(PROCESS-DEFAULT-SUBROUTINES)
(ACCESS-PRESUB)
(ACCESS-MODIFYSUB)
(ACCESS-CORRECTNESS-THM)
(CONSTRUCT-PRESUB-LIST)
(CONSTRUCT-MODIFYSUB-LIST)
(CONSTRUCT-PREMODIFY-LIST)
(INSTANCE-HINT)
(PRE-MODIFY-NEXT-CUTPOINT)
(PROCESS-NONTRIVIAL-SUBROUTINES)
(DEFSIMULATE+-FN)
(TRY-NEXT
 (1 1 (:TYPE-PRESCRIPTION TRY-NEXT))
 )
(TRY-RUN
 (6 6 (:TYPE-PRESCRIPTION TRY-NEXT))
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(TRY-PRECONDITION)
(TRY-INMAIN)
(TRY-CUTPOINT)
(TRY-ASSERTION)
(TRY-MODIFY)
($$$INSUB)
($$$PRESUB)
($$$MODIFYSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$PRESUB-IMPLIES-INSUB)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-test|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-base|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-step|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-fn|
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|))
 )
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-DEF|)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
($$$STEPS-TO-EXITPOINT-SUB-TAIL-DEF
 (12 12 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
($$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF)
($$$STEPS-TO-EXITPOINT-SUB
 (8 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
($$$NEXT-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB-SUFF)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 )
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION)
($$$ASSERTION-MAIN-IMPLIES-POST)
($$$ASSERTION-IMPLIES-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-test|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-base|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-step|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-DEF|)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL-DEF
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
($$$MAIN-STEPS-TO-EXITPOINT-TAIL$DEF)
($$$MAIN-STEPS-TO-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT-SUFF)
($$$NEXT-MAIN-EXITPOINT)
($$$CORRECTNESS-OF-MAIN)
(TRY-NEXT
 (1 1 (:TYPE-PRESCRIPTION TRY-NEXT))
 )
(TRY-RUN
 (6 6 (:TYPE-PRESCRIPTION TRY-NEXT))
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(TRY-INSUB)
(TRY-SUB-PRECONDITION)
(TRY-SUB-MODIFY)
(TRY-STEPS-TO-EXITPOINT-TAIL-SUB)
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-defpun-test|)
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-defpun-base|)
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION TRY-NEXT))
 )
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-defpun-stn|))
 )
(|TRY-STEPS-TO-EXITPOINT-TAIL-SUB-arity-1-DEF|)
(TRY-STEPS-TO-EXITPOINT-TAIL-SUB)
(TRY-STEPS-TO-EXITPOINT-TAIL-SUB-DEF
 (12 12 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TRY-STEPS-TO-EXITPOINT-TAIL-SUB$DEF
 (1 1 (:TYPE-PRESCRIPTION TRY-NEXT))
 )
(TRY-STEPS-TO-EXITPOINT-SUB)
(TRY-NEXT-EXITPOINT-SUB)
(TRY-EXISTS-EXITPOINT)
(TRY-EXISTS-EXITPOINT-SUFF)
(CORRECTNESS-OF-TRY)
(TRY-PRECONDITION)
(TRY-INMAIN)
(TRY-CUTPOINT)
(TRY-ASSERTION)
(TRY-MODIFY)
($$$INSUB)
($$$PRESUB)
($$$MODIFYSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$PRESUB-IMPLIES-INSUB)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-test|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-base|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-step|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-fn|
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|))
 )
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-DEF|)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
($$$STEPS-TO-EXITPOINT-SUB-TAIL-DEF
 (12 12 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
($$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF)
($$$STEPS-TO-EXITPOINT-SUB
 (8 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
($$$NEXT-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB-SUFF)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 )
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION)
($$$ASSERTION-MAIN-IMPLIES-POST)
($$$ASSERTION-IMPLIES-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-test|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-base|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-step|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-DEF|)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL-DEF
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
($$$MAIN-STEPS-TO-EXITPOINT-TAIL$DEF)
($$$MAIN-STEPS-TO-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT-SUFF)
($$$NEXT-MAIN-EXITPOINT)
($$$CORRECTNESS-OF-MAIN)
($$$PRESUB)
($$$MODIFYSUB)
($$$PRESUB-IMPLIES-INSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 )
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION)
($$$ASSERTION-MAIN-IMPLIES-POST)
($$$ASSERTION-IMPLIES-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-test|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-base|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-step|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-DEF|)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL-DEF
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
($$$MAIN-STEPS-TO-EXITPOINT-TAIL$DEF)
($$$MAIN-STEPS-TO-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT-SUFF)
($$$NEXT-MAIN-EXITPOINT)
(CORRECTNESS-WITH-ONE-SUB)
($$$PRESUB)
($$$MODIFYSUB)
($$$PRESUB-IMPLIES-INSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|))
 )
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 )
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION)
($$$ASSERTION-MAIN-IMPLIES-POST)
($$$ASSERTION-IMPLIES-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-test|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-base|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-step|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|)
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-defpun-stn|))
 )
(|$$$MAIN-STEPS-TO-EXITPOINT-TAIL-arity-1-DEF|)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL)
($$$MAIN-STEPS-TO-EXITPOINT-TAIL-DEF
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
($$$MAIN-STEPS-TO-EXITPOINT-TAIL$DEF)
($$$MAIN-STEPS-TO-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT)
($$$EXISTS-NEXT-EXITPOINT-SUFF)
($$$NEXT-MAIN-EXITPOINT)
(CORRECTNESS-WITH-TWO-SUBS)
