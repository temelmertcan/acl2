; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "../aux-functions")

(local
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(include-book "../eval-functions")

(include-book "../add-meta-rule-formula-checks")

(def-formula-checks-default-evl
 rp-evl
 (strip-cars *small-evl-fncs*))


(defun unquote-falist-keys (falist)
  (declare (xargs :guard t))
  (case-match falist
    #|(('quote ((('quote key) . val)))
     (hons-acons key val nil))||#
    (('quote ((('quote key) . val) . rest))
     (hons-acons key val
                 (unquote-falist-keys `',rest)))
    (''nil
     nil)
    (& falist)))

(defun quote-falist-vals (falist)
  (declare (xargs :guard t))
  (case-match falist
#|(('quote ((('quote key) . val)))
     (hons-acons key val nil))||#
    (('quote ((key . val) . rest))
     (hons-acons key (list 'quote val)
                 (quote-falist-vals `',rest)))
    (''nil
     nil)
    (& falist)))

;; special meta-like functions integrated into rp-rewriter.
(defun hons-acons-meta (term)
  (declare (xargs :guard t #|(pseudo-termp2 term)||#))
  ;; behaviour when hons-cons is encountered in the term
  ;; as if "hons-acons-meta" is a meta function triggered by hons-acons
  ;; this funciton stores assoc-lists in a special way in order to access the
  ;; elements in alists fast.
  (case-match term
    (('hons-acons ('quote key) val falist)
     (b* ((falist (ex-from-rp falist)))
       (case-match falist
         (('falist ('quote fa) ra)
          (mv
           `(falist ',(hons-acons key val fa)
                    (cons (cons ',key ,val)
                          ,ra))
           1 1))
         (''nil
          (mv
           `(falist ',(hons-acons key val nil)
                    (cons (cons ',key ,val) 'nil))
           1 1))
         (('quote fa)
          (if (alistp fa)
              (progn$
               (fast-alist-free fa)
               (mv `(falist ',(hons-acons key val (quote-falist-vals falist))
                            (cons (cons ',key ,val)
                                  ,falist))
                   1 1))
            (mv term #b1110 4)))
         (&
          (progn$
           #|(FMT-TO-COMMENT-WINDOW "Invalid hons-acons term ~p0 ~%"
                                  (list (cons #\0 term))
                                  0
                                  '(nil 8 10 nil)
                                  nil)||#
           (mv term #b1110 4))))))
    (& ;; otherwise return the term as is and let rewrite rules work it out.
     (progn$ (cw "Invalid hons-acons term (2) ~p0 ~%"
                 term)
             (mv term 1 1)))))

;; :i-am-here

;; (falist-consistent '(falist '((a . '5)
;;                               (b . '4))
;;                             '((a . 5)
;;                               (b . 4))))

;; (b* ((alist (make-fast-alist '((a . a-val)
;;                                (b . b-val))))
;;      ((mv res &)
;;       (hons-acons-meta `(hons-acons 'new-key new-val
;;                                     ',alist))))
;;   (list res (falist-consistent res)))

(encapsulate
  nil

  (def-formula-checks
   hons-acons-meta-formula-checks
   (hons-acons-meta
    hons-acons)))

(local
 (encapsulate
   nil

   (local
    (defthm lemma2
      (implies (and (pseudo-termp2 term)
                    (is-falist (ex-from-rp term)))
               (pseudo-termp2
                (caddr (ex-from-rp term))))))

   (defthm pseudo-termp2-hons-acons-meta ;;;;;;;;;;;;;;;;;;;;;;
     (implies (and (pseudo-termp2 term)
                   (all-falist-consistent term))
              (pseudo-termp2 (mv-nth 0 (hons-acons-meta term)))))))

(local
 (encapsulate
   nil

   (local
    (in-theory (enable is-rp)))

   (local
    (defthm lemma4
      (implies (and (all-falist-consistent term)
                    (is-falist (ex-from-rp term)))
               (falist-consistent-aux (cadr (cadr (ex-from-rp term)))
                                      (caddr (ex-from-rp term))))))

   (local
    (defthm lemma5
      (implies (and (all-falist-consistent term)
                    (is-falist (ex-from-rp term)))
               (all-falist-consistent (caddr (ex-from-rp term))))))


   (local
    (defthm lemma6
      (implies (and (alistp (cadr term))
                    (eq (car term) 'quote)
                    (consp (cdr term))
                    (not (cddr term))
                    (not (equal term ''nil)))
               (and (consp (cadr term))
                    (consp (car (cadr term)))))
      :rule-classes :forward-chaining))

   (defthm all-falist-consistent-hons-acons-meta
     (implies (and (all-falist-consistent term))
              (all-falist-consistent (mv-nth 0 (hons-acons-meta term))))
     :otf-flg t
     :hints (("goal" :in-theory (enable hons-acons-meta))))))

(local
 (defthmd rp-evl-of-ex-from-rp
   (equal (rp-evl (ex-from-rp term) a)
          (rp-evl term a))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp is-rp) ())))))

(local
 (encapsulate
   nil

   (local
    (defthmd lemma9-2
      (implies (syntaxp (equal term 'term))
               (equal (rp-evl (cadddr term) a)
                      (rp-evl (ex-from-rp (cadddr term)) a)))
      :hints (("Goal"
               :in-theory (e/d (rp-evl-of-ex-from-rp) ())))))

   (local
    (defthm lemma2
      (implies   (and (and (hons-acons-meta-formula-checks state)
                           (rp-evl-meta-extract-global-facts))
                      (consp term)
                      (EQUAL (CAR TERM) 'HONS-ACONS)
                      (CONSP (CDR TERM))
                      (CONSP (CDDR TERM))
                      (CONSP (CDDDR TERM))
                      (NOT (CDDR (CDDR TERM))))
                 (equal (RP-EVL TERM A)
                        (acons (rp-evl (cadr term) a)
                               (RP-EVL (CADDR TERM) A)
                               (RP-EVL (CADDDR TERM) A))))))

   (defthm rp-evl-of-hons-acons-meta
     (implies (and (hons-acons-meta-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evl (mv-nth 0 (hons-acons-meta term)) a)
                     (rp-evl term a)))
     :hints (("Goal"
              :in-theory (e/d (lemma9-2) ()))))))

(local
 (encapsulate
   nil
   (local
    (defthm lemma2
      (implies (and (is-falist term)
                    (valid-sc term a))
               (valid-sc (caddr term) a))
      :hints (("Goal"
               :expand (valid-sc (caddr term) a)
               :in-theory (e/d (is-if is-rp) (ex-from-rp))))))

   (defthm valid-sc-hons-meta
     (implies (valid-sc term a)
              (valid-sc (mv-nth 0 (HONS-ACONS-META term)) a))
     :hints (("Goal"
              :in-theory (e/d (is-rp is-if hons-acons-meta) ()))))))

(local
 (encapsulate
   nil
   (local
    (defthm lemma1
      (implies (and (is-falist term)
                    (rp-syntaxp term))
               (rp-syntaxp (caddr term)))
      :hints (("goal"
               :expand (valid-sc (caddr term) a)
               :in-theory (e/d (is-if is-rp) (ex-from-rp))))))
   (defthm rp-syntaxp-hons-acons
     (implies (rp-syntaxp term)
              (rp-syntaxp (mv-nth  0 (hons-acons-meta term)))))))

(local
 (defthm natp-dont-rw-hons-acons-meta
   (and (natp (mv-nth 1 (hons-acons-meta term)))
        (natp (mv-nth 2 (hons-acons-meta term))))
   :hints (("Goal"
            :in-theory (e/d ()
                            ())))))

(defthm hons-acons-meta-is-valid-rp-meta-rulep
  (implies (and (hons-acons-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'hons-acons-meta
                             :trig-fnc 'hons-acons
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (PSEUDO-TERMP2
                            hons-acons-meta
                            PSEUDO-TERM-LISTP2
                            RP-SYNTAXP
                            natp
                            VALID-SC)))))

(rp::add-meta-rules
 hons-acons-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'hons-acons-meta
        :trig-fnc 'hons-acons
        :dont-rw t
        :valid-syntax t)))
