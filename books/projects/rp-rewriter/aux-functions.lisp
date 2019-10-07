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

(include-book "std/lists/remove-duplicates" :dir :system)
(include-book "misc/beta-reduce" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/util/defines" :dir :system)

(include-book "std/strings/cat-base" :dir :system)

(include-book "macros" )

(local
 (include-book "ihs/ihs-lemmas" :dir :system))

;; Functions and lemmas used by both correctness proofs (rp-correct.lisp) and
;; guards (rp-rewriter.lisp)

(defun rp (prop term)
  (declare (ignorable prop))
  term)

(defun falist (fast-list term)
  (declare (ignorable fast-list))
  term)

(defconst *big-number*
  (1- (expt 2 60)))

(defun is-nonnil-fix (term)
  (declare (xargs :guard t))
  (case-match term (('nonnil-fix &) t) (& nil)))

(defun nonnil-p (term)
  (declare (xargs :guard t))
  (or (and (quotep term)
           (consp (cdr term)) ;; so that it is not (list 'quote)
           (not (equal (cadr term) 'nil)))
      (case-match term
        (('cons & &)
         t)
        (& nil))
;(is-nonnil-fix term)
      ))

(defun nonnil-listp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (equal lst nil)
    (and (nonnil-p (car lst))
         (nonnil-listp (cdr lst)))))

(defun nonnil-fix (x)
  (if x x t))

(defthm not-nonnil-fix
  (equal (not (nonnil-fix x))
         nil))

(encapsulate
  nil

  (defun beta-reduce-lamdas (term limit)
    (declare (xargs :measure (acl2-count limit)
                    :guard (and (natp limit))))
    ;; gets a term that could be a cascade of lambda expressions and turns it into
    ;; a regular expression.
    (if (zp limit)
        term
      (if (atom term)
          term
        (if (and (acl2::flambda-applicationp term)
                 (pseudo-termp term))
            (beta-reduce-lamdas (acl2::beta-reduce-lambda-expr term)
                                (1- limit))
          term))))

  (mutual-recursion
   ;; searchs all the lambda terms and performs beta reduction on them.

   (defun beta-search-reduce (term limit)
     (declare (xargs :measure  (nfix limit)
                     :guard (and (natp limit))))
     (if (or (atom term)
             (quotep term)
             (zp limit))
         term
       (if (and (acl2::lambda-expr-p term)
                (pseudo-termp term))
           ;; !!!! PSEUDO-TERMP IS FOR THE GUARD. PROBABLY  BAD FOR RUNTIME!!!
           ;; it is ok for the time being because this function is not intended
           ;; for big terms.
           (beta-search-reduce (acl2::beta-reduce-lambda-expr term)
                               (1- limit))
         (cons (car term)
               (beta-search-reduce-subterms (cdr term) (1- limit))))))

   (defun beta-search-reduce-subterms (subterms limit)
     (declare (xargs :measure  (nfix limit)
                     :guard (and (natp limit))))
     (if (or (zp limit)
             (atom subterms))
         subterms
       (cons (beta-search-reduce (car subterms) (1- limit))
             (beta-search-reduce-subterms (cdr subterms) (1- limit)))))))

(define is-rp (term)
  :inline t
  (case-match term (('rp ('quote type) &)
                    (and (symbolp type)
                         (not (booleanp type))
                         (not (equal type 'quote))
                         (not (equal type 'rp))))
    (& nil))
  ///
  (defthmd is-rp-implies
    (implies (is-rp term)
             (case-match term
               (('rp ('quote type) &)
                (and (symbolp type)
                     (not (booleanp type))
                     (not (equal type 'quote))))
               (& nil)))))
(define is-if (term)
  :inline t
  (case-match term (('if & & &) t)
    (& nil)))

(define is-return-last (term)
  :enabled t
  :inline t
  (case-match term (('return-last & & &) t)
    (& nil)))

(define is-rp-soft (term)
  :enabled t
  :inline t
  (case-match term (('rp & &) t)
    (& nil)))

(define is-lambda (term)
  (case-match term
    ((('lambda & &) .  &)
     t)
    (& nil)))

(defun is-member (e lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (or (equal e (car lst))
        (is-member e (cdr lst)))))

(defun union-equal2 (lst1 lst2)
  (declare (xargs :guard t))
  (cond ((atom lst1)
         lst2)
        ((is-member (car lst1) lst2)
         (union-equal2 (cdr lst1) lst2))
        (t
         (cons (car lst1)
               (union-equal2 (cdr lst1) lst2)))))

(defun remove-vars (big small)
  (declare (xargs :guard t))
  (if (atom big)
      nil
    (if (is-member (car big) small)
        (remove-vars (cdr big) small)
      (cons (car big)
            (remove-vars (cdr big) small)))))

(mutual-recursion
 (defun get-lambda-free-vars (term)
   (declare (xargs :guard t
                   :guard-hints (("Goal"
                                  :in-theory (e/d (is-lambda) ())))))
   (cond
    ((atom term) (mv t (list term)))
    ((quotep term) (mv t nil))
    ((is-lambda term)
     (b* (((mv valid sub-vars) (get-lambda-free-vars (caddr (car term))))
          (lambda-vars (cadr (car term)))
          ((mv valid-2 global-vars) (get-lambda-free-vars-lst (cdr term))))
       (mv (and valid
                valid-2
                (equal (remove-vars sub-vars lambda-vars) nil))
           global-vars)))
    (t (get-lambda-free-vars-lst (cdr term)))))

 (defun get-lambda-free-vars-lst (lst)
   (if (atom lst)
       (mv t nil)
     (b* (((mv valid-1 vars-1)
           (get-lambda-free-vars (car lst)))
          ((mv valid-2 vars-2)
           (get-lambda-free-vars-lst (cdr lst))))
       (mv (and valid-1 valid-2)
           (union-equal2 vars-1 vars-2))))))

#|(encapsulate
  nil
  (local
   (make-flag get-lambda-free-vars :defthm-macro-name
              defthm-get-lambda-free-vars))
  (local
   (defthm-get-lambda-free-vars
     (defthm true-listp-get-lambda-free-vars
       (true-listp (get-lambda-free-vars term))
       :flag get-lambda-free-vars)

     (defthm true-listp-get-lambda-free-vars-lst
       (true-listp (get-lambda-free-vars-lst lst))
       :flag get-lambda-free-vars-lst)))

  (verify-guards get-lambda-free-vars-lst))||#

(mutual-recursion
 (defun lambda-exp-free-p (term)
   (declare (xargs :guard t :mode :logic))
   (cond ((atom term) t)
         ((eq (car term) 'quote)
          t)
         (t (and (atom (car term))
                 (lambda-exp-free-listp (cdr term))))))

 (defun lambda-exp-free-listp (subterms)
   (if (atom subterms)
       (eq subterms nil)
     (and (lambda-exp-free-p (car subterms))
          (lambda-exp-free-listp (cdr subterms))))))

(encapsulate
  nil

  (define is-lambda-strict (x)
    :prepwork ((local (in-theory (enable is-lambda))))
    (and (is-lambda x)
         (symbol-listp (cadr (car x)))
         (equal (len (cadr (car x)))
                (len (cdr x)))
;(lambda-exp-free-listp (cdr x)) ;; variables should not have lambda expressions
         (b* (((mv valid &)
               (get-lambda-free-vars x)))
           valid)))

  (local
   (in-theory (enable is-rp
                      is-lambda
                      is-lambda-strict
                      is-rp-soft)))

  (mutual-recursion
   (defun pseudo-termp2 (acl2::x)
     ;; same as pseudo-termp but does not allow nil as a symbol
     (declare (xargs :guard t :mode :logic))
     (cond ((atom acl2::x) (and (symbolp acl2::x) acl2::x))
           ((eq (car acl2::x) 'quote)
            (and (consp (cdr acl2::x))
                 (null (cdr (cdr acl2::x)))))
           ((not (true-listp acl2::x)) nil)
           #|((and (is-rp acl2::x)
           (is-rp (caddr acl2::x)))
           nil)||#
           #|((eq (car acl2::x) 'rp)
           (and (is-rp acl2::x)
           (pseudo-termp2 (caddr acl2::x))))||#
           ((not (pseudo-term-listp2 (cdr acl2::x)))
            nil)
           (t (and (symbolp (car acl2::x))
                   (car acl2::x)
                   #|(and
                   (is-lambda-strict acl2::x)
                   (pseudo-termp2 (caddr (car acl2::x))))||#))))

   (defun pseudo-term-listp2 ( acl2::lst)
     (declare (xargs :guard t))
     (cond ((atom acl2::lst) (equal acl2::lst nil))
           (t (and (pseudo-termp2 (car acl2::lst))
                   (pseudo-term-listp2 (cdr acl2::lst)))))))

  (defun pseudo-term-list-listp2 (lst)
    (declare (xargs :guard t))
    (if (atom lst)
        (equal lst nil)
      (and (pseudo-term-listp2 (car lst))
           (pseudo-term-list-listp2 (cdr lst))))))

(encapsulate
  nil
  (local
   (in-theory (enable is-rp)))
  (mutual-recursion
   ;; checks if all the terms with a function symbol
   ;; "rp" satisfies the is-rp condition.
   (defun rp-syntaxp (term)
     (declare (xargs :guard t))
     (cond
      ((atom term) t)
      ((eq (car term) 'quote) t)
      ((eq (car term) 'rp)
       (and (is-rp term)
            (rp-syntaxp (caddr term))))
      (t (rp-syntaxp-lst (cdr term)))))
   (defun rp-syntaxp-lst (lst)
     (cond
      ((atom lst) t)
      (t (and (rp-syntaxp (car lst))
              (rp-syntaxp-lst (cdr lst))))))))

(defun rp-syntaxp-bindings (bindings)
  (rp-syntaxp-lst (strip-cdrs bindings)))

(defthm pseudo-termp2-implies-cdr-listp
  (implies (and (consp term)
                (pseudo-termp2 term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp2 (cdr term)))
  :hints (("Goal"
           :Expand ((PSEUDO-TERMP2 TERM)
                    (PSEUDO-TERM-LISTP2 (CDR TERM))
                    (PSEUDO-TERM-LISTP2 (CdDR TERM)))
           :in-theory (e/d (is-rp) ()))))

(encapsulate
  nil
  (define fnc-alistp (fnc-alist)
    :enabled t
    (if (atom fnc-alist)
        (equal fnc-alist nil)
      (and (consp (car fnc-alist))
           (symbolp (caar fnc-alist))
           (natp (cdar fnc-alist))
           (fnc-alistp (cdr fnc-alist)))))

  (defmacro bindings-alistp (bindings)
    `(and (alistp ,bindings)
          (symbol-listp (strip-cars ,bindings))
          (pseudo-term-listp2 (strip-cdrs ,bindings)))))

(defun cons-count (x)
  (cond ((atom x)
         1)
        (t
         (+ (cons-count (car x))
            (cons-count (cdr x))))))

(mutual-recursion
 (defun count-lambdas (x)
   (declare (xargs :guard t
                   :guard-hints (("Goal"
                                  :in-theory (e/d (is-lambda is-lambda-strict) ())))))
   (cond ((atom x) 0)
         ((eq (car x) 'quote) 0)
         ((is-lambda-strict x)
          (+ 1
             (count-lambdas (caddr (car x)))))
         (t (count-lambdas-lst (cdr x)))))

 (defun count-lambdas-lst (lst)
   (if (atom lst)
       0
     (+ (count-lambdas (car lst))
        (count-lambdas-lst (cdr lst))))))

(defun cons-consp (lst)
  (declare (xargs :guard t))
  ;;  all the elements should be conses and not quoteps
  (if (atom lst)
      (equal lst nil)
    (and (consp (car lst))
         (not (quotep (car lst)))
         (cons-consp (cdr lst)))))

(mutual-recursion
 (defun include-fnc (term fnc)
   (declare (xargs :guard (and #|(pseudo-termp2 term)||#
                           (symbolp fnc))))
   (if (or (atom term)
           (quotep term))
       nil
     (if (eq (car term) fnc)
         t
       (or
        #|(include-fnc (car term) fnc)||#
        (include-fnc-subterms (cdr term) fnc)))))

 (defun include-fnc-subterms (subterms fnc)
   (declare (xargs :guard (and #|(pseudo-term-listp2 subterms)||#
                           (symbolp fnc))))
   (if (atom subterms)
       nil
     (or (include-fnc (car subterms) fnc)
         (include-fnc-subterms (cdr subterms) fnc)))))

(defun is-honsed-assoc-eq-values (term)
  (declare (xargs :guard t))
  (case-match term
    (('assoc-eq-vals ('quote &) ('falist ('quote &) &))
     t)
    (& nil)))

(encapsulate
  nil

  (local
   (in-theory (enable is-rp)))

  (defun-inline is-synp (term)
    (declare (xargs :guard t #|(and (pseudo-termp2 term))||#))
    (case-match term (('synp & & &) t) (& nil)))

  (defund-inline is-rp-loose (term)
    (declare (xargs :guard t #|(and (pseudo-termp2 term))||#))
    (case-match term (('rp & &) t) (& nil)))

  (defun ex-from-rp (term)
    (declare (xargs :guard t))
    (mbe :logic (if (is-rp term) (ex-from-rp (caddr term)) term)
         :exec (if (case-match term
                     (('rp ('quote type) &)
                      (and (symbolp type)
                           (not (booleanp type))
                           (not (equal type 'quote))
                           (not (equal type 'rp))))
                     (& nil))
                   (ex-from-rp (caddr term))
                 term)))

  (local
   (in-theory (enable IS-RP-LOOSE)))

  (defund-inline ex-from-rp-loose (term)
    (declare (xargs :guard t))
    (mbe :logic (if (is-rp-loose term)
                    (ex-from-rp-loose (caddr term))
                  term)
         :exec (case-match term (('rp & x)
                                 (ex-from-rp-loose x))
                 (& term))))

  (local
   (in-theory (enable ex-from-rp-loose)))

  (defun extract-from-rp-with-context (term context)
    (declare (xargs :guard t #|(pseudo-termp2 term)||#))
    (case-match term
      (('rp ('quote type) x)
       (if (and (symbolp type)
                (not (booleanp type))
                (not (equal type 'rp))
                (not (equal type 'quote)))
           (b* (((mv rcontext rterm)
                 (extract-from-rp-with-context x context)))
             (mv (cons `(,type ,(ex-from-rp x)) rcontext) rterm))
         (mv context term)))
      (& (mv context term))))

  (defun extract-from-synp (term)
    (declare (xargs :guard t #|(pseudo-termp2 term)||#))
    (case-match term
      (('synp & & &) ''t)
      (& term)))

  (defun ex-from-synp (term)
    (if (is-synp term)
        ''t
      term))

  (defun-inline is-cons (term)
    (declare (xargs :guard (and t)))
    (case-match term (('cons & &) t) (& nil)))

  (defun-inline is-quoted-pair (term)
    (declare (xargs :guard (and t)))
    (and #|(quotep term)||#
     (consp term)
     (eq (car term) 'quote)
     (consp (cdr term))
     (consp (unquote term))))

  (defun-inline should-term-be-in-cons (rule-lhs term)
    (declare (xargs :guard t #|(and (pseudo-termp2 term)
                    (pseudo-termp2 rule-lhs))||#))
    (and (is-quoted-pair term) ;(quotep term)
         ;;(consp (unquote term))
         (is-cons rule-lhs);;(case-match rule-lhs (('cons & &) t) (& nil))
         ))

  (defun-inline put-term-in-cons (term)
    (declare (xargs :guard (and #|(pseudo-termp2 term)||#
                            (should-term-be-in-cons '(cons x y) term))))
    `(cons ',(car (unquote term))
           ',(cdr (unquote term))))

  (defund context-from-rp (term context)
    (if (is-rp term)
        (let ((type (car (cdr (car (cdr term)))))
              (x (car (cdr (cdr term)))))
          (b* ((rcontext (context-from-rp x context)))
            (cons (cons type (cons (ex-from-rp x) 'nil))
                  rcontext)))
      context)))

(defun-inline dumb-negate-lit2 (term)
  (declare (xargs :guard t #|(pseudo-termp2 term)||#))
  (cond ((atom term)
         (acl2::fcons-term* 'not term))
        ((acl2::fquotep term)
         (cond ((equal term ''nil)
                ''t)
               (t ''nil)))
        ((case-match term (('not &) t) (& nil))
         (acl2::fargn term 1))
        ((and (case-match term (('equal & &) t) (& nil))
              (or (equal (acl2::fargn term 2)
                         ''nil)
                  (equal (acl2::fargn term 1)
                         ''nil)))
         (if (equal (acl2::fargn term 2)
                    ''nil)
             (acl2::fargn term 1)
           (acl2::fargn term 2)))
        (t (acl2::fcons-term* 'not term))))

(encapsulate
  nil

  (mutual-recursion
   (defun get-vars1 (q acc)
     (declare (xargs :guard (and (true-listp acc)
                                 #|(pseudo-termp2 q)||#)
                     :verify-guards nil))
     (if (quotep q)
         acc
       (if (atom q)
           (if (member-equal q acc) acc (cons q acc))
         (get-vars-subterms (cdr q) acc))))

   (defun get-vars-subterms (subterms acc)
     (declare (xargs :guard (and (true-listp acc)
                                 #|(pseudo-term-listp2 subterms)||#)
                     :verify-guards nil))
     (if (atom subterms)
         acc
       (get-vars-subterms (cdr subterms)
                          (get-vars1 (car subterms) acc)))))

  (make-flag get-vars1 :defthm-macro-name defthm-get-vars1)

  (defthm-get-vars1
    (defthm true-listp-get-vars1
      (implies (true-listp acc)
               (true-listp (get-vars1 q acc)))
      :flag get-vars1)
    (defthm true-listp-get-vars-subterms
      (implies (true-listp acc)
               (true-listp (get-vars-subterms subterms acc)))
      :flag get-vars-subterms))

  (verify-guards get-vars1)

  (defun get-vars (term)
    (declare (xargs :guard t #|(pseudo-termp2 term)||#))
    (get-vars1 term nil)))

(encapsulate
  nil
  (defrec custom-rewrite-rule
    ((lhs . flg) (hyp . hyp-dont-rw) (rhs dont-rw . dont-rw-size) . (rune . rule-fnc))
    t) ; t when we are confident that the code is OK

  (defun weak-custom-rewrite-rule-listp (rules)
    (declare (xargs :guard t))
    (if (atom rules)
        (eq rules nil)
      (and (weak-custom-rewrite-rule-p (car rules))
           (weak-custom-rewrite-rule-listp (cdr rules)))))

  (defun-inline rp-hyp (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :hyp))

  (defun-inline rp-lhs (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :lhs))

  (defun-inline rp-rhs (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :rhs))

  (defun-inline rp-rune (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :rune))

  (defun-inline rp-iff-flag (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :flg))

  (defun-inline rp-rule-fnc (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :rule-fnc))

  (defun-inline rp-hyp-dont-rw (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :hyp-dont-rw))

  (defun-inline rp-dont-rw (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :dont-rw))

  (defun-inline rp-dont-rw-size (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :dont-rw-size)))

(encapsulate
  nil

  (defmacro rp-hypm (rule)
    ;; return hyps from a given rule

    `(access custom-rewrite-rule ,rule :hyp))

  (defmacro rp-lhsm (rule)
    ;; return hyps from a given rule
    `(access custom-rewrite-rule ,rule :lhs))

  (defmacro rp-rhsm (rule)
    ;; return hyps from a given rule
    `(access custom-rewrite-rule ,rule :rhs))

  (defmacro rp-runem (rule)
    ;; return hyps from a given rule
    `(access custom-rewrite-rule ,rule :rune))

  (defmacro rp-iff-flagm (rule)
    `(access custom-rewrite-rule ,rule :flg)))

#|(encapsulate
  nil
  (defstobj rp-stat
    (rules-used :type t :initially nil)
    (save-rules-used :type t :initially nil))

  (defun add-to-rules-used (rule rp-stat)
    (declare (xargs
              :guard (and (weak-custom-rewrite-rule-p rule)
                          (RP-STATP RP-STAT))
              :stobjs rp-stat))
    (if (save-rules-used rp-stat)
        (update-rules-used (cons (rp-rule-name rule)
                                 (rules-used rp-stat))
                           rp-stat)
      rp-stat))

  (defun add-to-rules-used-with-rule-name (rule-name rp-stat)
    (declare (xargs
              :GUARD (rp-statp rp-stat)
              :stobjs rp-stat))
    (if (save-rules-used rp-stat)
        (update-rules-used (cons rule-name
                                 (rules-used rp-stat))
                           rp-stat)
      rp-stat))

  (defun finalize-rules-used (rp-stat)
    (declare (xargs
              :GUARD (RP-STATP RP-STAT)
              :stobjs rp-stat))
    (if (save-rules-used rp-stat)
        (update-rules-used
         (acl2::hons-remove-duplicates (rules-used rp-stat) )
         rp-stat)
      rp-stat))

  (defun reset-rp-stat (rp-stat)
    (declare (xargs
              :GUARD (RP-STATP RP-STAT)
              :stobjs rp-stat))
    (b* ((rp-stat (update-rules-used nil rp-stat)))
      rp-stat)))||#

(defun remove-from-alist (alist key)
  (declare (xargs :guard t))
  (if (atom alist)
      alist
    (if (not (consp (car alist)))
        alist
      (if (equal (caar alist) key)
          (remove-from-alist (cdr alist) key)
        (cons-with-hint (car alist)
                        (remove-from-alist (cdr alist) key)
                        alist)))))

(encapsulate
  nil

  (define dont-rw-if-fix (dont-rw)
    (case-match
      dont-rw
      ((& & & &)
       dont-rw)
      (& '(nil nil nil nil)))
    ///
    (local
     (defthmd dont-rw-if-fix-type
       (let ((res (dont-rw-if-fix dont-rw)))
         (and (consp res)
              (consp (cdr res))
              (consp (cddr res))
              (consp (cdddr res))
              (equal (cddddr res) nil))))))

  (define strict-quotep (term)
    :enabled t
    (and (consp term)
         (eq (car term) 'quote)
         (consp (cdr term))
         (not (cddr term))))

  #|(defun dont-rw-syntaxp-aux (dont-rw)
    (declare (xargs :guard t))
    (if (atom dont-rw)
        t
      (and (or (atom (car dont-rw))
;(strict-quotep (car dont-rw))
               (dont-rw-syntaxp-aux (car dont-rw)))
           (dont-rw-syntaxp-aux (cdr dont-rw)))))||#

  #|(defun dont-rw-syntaxp-aux (dont-rw)
  (declare (xargs :guard t))
  (if (atom dont-rw)
  (equal dont-rw nil)
  (and (or (booleanp (car dont-rw))
  (dont-rw-syntaxp-aux (car dont-rw)))
  (dont-rw-syntaxp-aux (cdr dont-rw)))))||#

  #|(defund dont-rw-syntaxp (dont-rw)
    (declare (xargs :guard t))
    (or (atom dont-rw)
        ;;(strict-quotep dont-rw)
        (dont-rw-syntaxp-aux dont-rw)))||#

  (define should-not-rw (dont-rw)
    :guard (integerp dont-rw)
    :inline t
    (= (acl2::logcar dont-rw) 1))

  #|(defund dont-rw-syntax-fix (dont-rw)
    (declare (xargs :guard t))
    (if (dont-rw-syntaxp dont-rw)
        dont-rw
      (progn$ (hard-error 'dont-rw-syntax-fix
                          "this dont'rw is being fixed. This should have
    not happened... ~p0 ~%"
                          (list (cons #\0 dont-rw)))
              t)))||#)

(encapsulate
  nil

  (defun falist-consistent-aux (falist term)
    ;; given an unquoted falist (a fast alist from (falist & &)), compares it
    ;; with the term and makes sure that they're consistent.
    (declare (xargs :guard t))
    (if (atom falist)
        (and (equal falist nil)
             (equal term ''nil))
      (b* ((cf (car falist))
           (cf-key (if (consp cf) (car cf) nil))
           (cf-val (if (consp cf) (cdr cf) nil)))
        (and
         (consp cf)
         (case-match term
           (('cons ('cons ('quote key1) val1) rest1)
            (and (equal cf-key key1)
                 (equal cf-val val1)
                 (falist-consistent-aux (cdr falist)
                                        rest1)))
           (('cons ('quote (key1 . val1)) rest1)
            (and #|(if (equal key1 nil)
             (equal cf-key (list 'quote))
             nil)||#
             (equal cf-key key1)
             (equal cf-val (list 'quote val1))
             (falist-consistent-aux (cdr falist)
                                    rest1)))
           (('quote ((key1 . val1) . rest1))
            (and (equal cf-key key1)
                 (equal cf-val (list 'quote val1))
                 (falist-consistent-aux (cdr falist)
                                        `',rest1)))
           (& nil))))))

  (defun falist-consistent (falist-term)
    ;; given a falist term (falist & &), checks the consistence.
    (declare (xargs :guard t))
    (case-match falist-term
      (('falist ('quote falist) term)
       (falist-consistent-aux falist term))
      (('falist ''nil ''nil)
       t)
      (& nil)))

  (defun falist-syntaxp (unquoted-falist)
    ;; on the unquoted fast-alist (which is the first parameter of (falist & &)
    ;; but unquoted), checks the syntacial correctness
    (declare (xargs :guard t))
    (and (alistp unquoted-falist)
         (pseudo-term-listp2
          (strip-cdrs unquoted-falist))))

  (defun is-falist (term)
    ;; checks if it is a falist statement?
    (declare (xargs :guard t))
    (case-match term (('falist & &) t) (& nil)))

  (mutual-recursion
   (defun all-falist-consistent (term)
     ;; searches the term for (falist & &) and if found, checkes whether
     ;; they're consistent.
     (declare (xargs :guard t #|(pseudo-termp2 term)||#))
     (cond
      ((or (atom term)
           (quotep term))
       t)
      ((is-falist term)
       (and (falist-consistent term)
            (all-falist-consistent (caddr term))))
      (t (all-falist-consistent-lst (cdr term)))))

   (defun all-falist-consistent-lst (lst)
     (declare (xargs :guard t #|(pseudo-term-listp2 lst)||#))
     (if (atom lst)
         t
       (and (all-falist-consistent (car lst))
            (all-falist-consistent-lst (cdr lst))))))

  (defun all-falist-consistent-bindings (bindings)
    ;; input is var-bindings;
    ;; checks if the values are falist-consistent
    (if (atom bindings)
        t
      (and (consp (car bindings))
           (all-falist-consistent (cdar bindings))
           (all-falist-consistent-bindings (cdr bindings))))))

(defun context-syntaxp (context)
  (declare (xargs :guard t))
  (and ;(cons-consp context) ;; may not be necessary anymore.
;(not (member nil context))
   (pseudo-term-listp2 context)
   (rp-syntaxp-lst context)
   (all-falist-consistent-lst context)))

(mutual-recursion

 (defun remove-return-last (term)
   (declare (xargs :guard t #|(pseudo-termp2 term)||#))
   (cond
    ((or (atom term)
         (quotep term)
         (is-falist term))
     term)
    ((is-return-last term)
     (remove-return-last (cadddr term)))
    (t (cons (car term)
             (remove-return-last-subterms (cdr term))))))

 (defun remove-return-last-subterms (subterms)
   (declare (xargs :guard t #|(pseudo-term-listp2 subterms)||#))
   (if (atom subterms)
       subterms
     (cons (remove-return-last (car subterms))
           (remove-return-last-subterms (cdr subterms))))))

(defund is-hide (term)
  (declare (xargs :guard t))
  (case-match term
    (('hide &) t)
    (& nil)))

(in-theory (disable extract-from-rp-with-context))

(mutual-recursion
 (defun search-term (term seq)
   ;; case insensitive search on the term
   (cond ((atom term)
          (search seq (symbol-name term)  :test 'char-equal))
         ((quotep term)
          nil)
         ((consp (car term))
          (or (search-subterms (car term) seq)
              (search-subterms (cdr term) seq)))
         (t
          (or (search seq (symbol-name (car term)) :test 'char-equal)
              (search-subterms (cdr term) seq)))))
 (defun search-subterms (subterms seq)
   (if (atom subterms)
       nil
     (or (search-term (car subterms) seq)
         (search-subterms (cdr subterms) seq)))))

(defmacro rp-valid-termp (term)
  `(and (pseudo-termp2 ,term)
        (rp-syntaxp ,term)
        (all-falist-consistent ,term)))

(defun rp-valid-term-listp (terms)
  (if (atom terms)
      (equal terms nil)
    (and (rp-valid-termp (car terms))
         (rp-valid-term-listp (cdr terms)))))

(encapsulate
  nil

  (local
   (defthm consp-extract-from-rp
     (implies (consp (ex-from-rp term))
              (consp term))))

  (local
   (defthm consp-ex-from-rp-loose
     (implies (consp (ex-from-rp-loose term))
              (consp term))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp-loose
                               is-rp-loose) ())))))

  (local
   (defthm extract-from-rp-acl2-count
     (implies (consp term)
              (< (acl2-count (cdr (ex-from-rp term)))
                 (acl2-count term)))))

  (local
   (defthm ex-from-rp-loose-acl2-count
     (implies (consp term)
              (< (acl2-count (cdr (ex-from-rp-loose term)))
                 (acl2-count term)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp-loose
                               is-rp-loose) ())))))

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp terms
   (defun rp-equal (term1 term2)
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard t #|(and (pseudo-termp2 term1)
                     (pseudo-termp2 term2))||#))
     "Check syntactic equivalance of two terms by ignoring all the rp terms"
     (let* ((term1 (ex-from-rp term1))
            (term2 (ex-from-rp term2)))
       (cond
        ((or (atom term1)
             (atom term2)
             (acl2::fquotep term1)
             (acl2::fquotep term2))
         (equal term1 term2))
        (t (and (equal (car term1) (car term2))
                (rp-equal-subterms (cdr term1) (cdr term2)))))))

   (defun rp-equal-subterms (subterm1 subterm2)
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard t #|(and (pseudo-term-listp2 subterm1)
                     (pseudo-term-listp2 subterm2))||#))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal (car subterm1) (car subterm2))
            (rp-equal-subterms (cdr subterm1) (cdr subterm2))))))

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp terms
   (defun rp-equal-loose (term1 term2)
     (declare (xargs :mode :logic
                     :verify-guards nil
;           :measure (+ (cons-count term1)
;                      (cons-count term2))
                     :guard t #|(and (pseudo-termp2 term1)
                     (pseudo-termp2 term2))||#))
     "Check syntactic equivalance of two terms by ignoring all the rp terms"
     (let* ((term1 (ex-from-rp-loose term1))
            (term2 (ex-from-rp-loose term2)))
       (cond
        ((or (atom term1) (atom term2)
             (acl2::fquotep term1) (acl2::fquotep term2))
         (equal term1 term2))
        (t (and (equal (car term1) (car term2))
                (rp-equal-loose-subterms (cdr term1) (cdr term2)))))))

   (defun rp-equal-loose-subterms (subterm1 subterm2)
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard t #|(and (pseudo-term-listp2 subterm1)
                     (pseudo-term-listp2 subterm2))||#))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal-loose (car subterm1) (car subterm2))
            (rp-equal-loose-subterms (cdr subterm1) (cdr subterm2))))))

  #|(defun rp-equal3 (terms1 terms2)
  (declare (xargs :mode :logic
  :verify-guards t
  :measure (cons-count terms1)
  :guard t #|(and (pseudo-term-listp2 subterm1)
  (pseudo-term-listp2 subterm2))||#))
  (if (or (atom terms1)
  (atom terms2))
  (equal terms1 terms2)
  (b* ((first1 (ex-from-rp-loose (car terms1)))
  (first2 (ex-from-rp-loose (car terms2))))
  (cond ((or (atom first1)
  (atom first2)
  (eq (car first1) 'quote)
  (eq (car first2) 'quote))
  (and (equal first1 first2)
  (rp-equal3 (cdr terms1) (cdr terms2))))
  (t (and (equal (car first1) (car first2))
  (rp-equal3 (cdr first1) (cdr first2))
  (rp-equal3 (cdr terms1) (cdr terms2))))))))||#

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp terms
   (defun rp-equal-cnt (term1 term2 cnt)
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard (and (integerp cnt)
                                 #|(pseudo-termp2 term1)||#
                                 #|(pseudo-termp2 term2)||#)))
     "Same as rp-equal but also runs equal after counter goes below 0."
     (or (if (and (< cnt 0))
             (equal term1 term2)
           nil)
         (let* ((term1 (ex-from-rp term1))
                (term2 (ex-from-rp term2)))
           (cond
            ((or (atom term1) (atom term2)
                 (acl2::fquotep term1)
                 (acl2::fquotep term2))
             (equal term1 term2))
            (t ;(or (if (< cnt 0) (equal term1 term2) nil)
             (and (equal (car term1) (car term2))
                  (rp-equal-cnt-subterms (cdr term1) (cdr term2) (1- cnt))))))))

   (defun rp-equal-cnt-subterms (subterm1 subterm2 cnt)
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard (and (integerp cnt)
                                 #|(pseudo-term-listp2 subterm1)||#
                                 #|(pseudo-term-listp2 subterm2)||#)))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal-cnt (car subterm1) (car subterm2) cnt)
            (rp-equal-cnt-subterms (cdr subterm1) (cdr subterm2) cnt)))))

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp terms
   (defun p-rp-equal-cnt (term1 term2 cnt)
     (declare (xargs :mode :program))
     "Same as rp-equal but also runs equal after counter goes below 0."
     (or (if (and (< cnt 0))
             (equal term1 term2)
           nil)
         (let* ((term1 (ex-from-rp-loose term1))
                (term2 (ex-from-rp-loose term2)))
           (cond
            ((or (atom term1) (atom term2)
                 (acl2::fquotep term1)
                 (acl2::fquotep term2))
             (equal term1 term2))
            (t ;(or (if (< cnt 0) (equal term1 term2) nil)
             (and (equal (car term1) (car term2))
                  (p-rp-equal-cnt-subterms (cdr term1) (cdr term2) (1- cnt))))))))

   (defun p-rp-equal-cnt-subterms (subterm1 subterm2 cnt)
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (p-rp-equal-cnt (car subterm1) (car subterm2) cnt)
            (p-rp-equal-cnt-subterms (cdr subterm1) (cdr subterm2) cnt))))))

(encapsulate
  nil

  (local
   (in-theory (disable rp-hyp rp-lhs rp-rhs)))

  (defun no-free-variablep (rule)
    (declare (xargs :guard (and (weak-custom-rewrite-rule-p rule)
                                (pseudo-termp2 (rp-hyp rule))
                                (pseudo-termp2 (rp-lhs rule))
                                (pseudo-termp2 (rp-rhs rule)))))
    (let ((vars (get-vars (rp-lhs rule))))
      (and (subsetp (get-vars (rp-hyp rule))
                    vars
                    :test 'equal)
           (subsetp (get-vars (rp-rhs rule))
                    vars
                    :test 'equal))))

  (defun rule-syntaxp (rule)
    (declare (xargs :guard t))
    (and
     (weak-custom-rewrite-rule-p rule)
     (pseudo-termp2 (rp-hyp rule))
     (pseudo-termp2 (rp-lhs rule))
     (pseudo-termp2 (rp-rhs rule))
     ;;(rp-syntaxp (rp-lhs rule))
     (not (include-fnc (rp-lhs rule) 'rp))
     (not (include-fnc (rp-hyp rule) 'rp))
     (rp-syntaxp (rp-rhs rule))

     (not (include-fnc (rp-rhs rule) 'falist))
     (not (include-fnc (rp-hyp rule) 'falist))
     (not (include-fnc (rp-lhs rule) 'if))
     (consp (rp-lhs rule))
     (not (acl2::fquotep (rp-lhs rule)))
     (not (include-fnc (rp-lhs rule) 'synp))

     (natp (rp-dont-rw-size rule))
     (natp (rp-dont-rw rule))
     (natp (rp-hyp-dont-rw rule))
     
     (no-free-variablep rule)))

  (defun rule-list-syntaxp (rules)
    (declare (xargs :guard t))
    (if (atom rules)
        t;(equal rules nil)
      (and (rule-syntaxp (car rules))
           (rule-list-syntaxp (cdr rules)))))

  (defun rule-list-list-syntaxp (rules)
    (declare (xargs :guard t))
    (if (atom rules)
        t;(equal rules nil)
      (and (rule-list-syntaxp (car rules))
           (rule-list-list-syntaxp (cdr rules)))))

  (defun rules-alistp (rules)
    (declare (xargs :guard t))
    (and (alistp rules)
         (symbol-listp (strip-cars rules))
         (rule-list-list-syntaxp (strip-cdrs rules)))))

(defun valid-term-syntaxp (term)
  (declare (xargs :guard t))
  (and (pseudo-termp2 term)
       (not (include-fnc term 'rp))
       (not (include-fnc term 'falist))))

(mutual-recursion
 (defun ex-from-rp-all (term)
   (cond ((atom term)
          term)
         ((is-rp term)
          (ex-from-rp-all (ex-from-rp term)))
         (t
          (cons (car term)
                (ex-from-rp-all-lst (cdr term))))))

 (defun ex-from-rp-all-lst (lst)
   (if (atom lst)
       nil
     (cons (ex-from-rp-all (car lst))
           (ex-from-rp-all-lst (cdr lst))))))

(encapsulate
  nil

  (defrec rp-meta-rule-rec
    (trig-fnc ;; trigger function name
     fnc ;; function name that meta rule executes
     dont-rw ;; if meta rule also returns a structure for dont-rw
     . valid-syntax ;; if meta rule returns valid-syntax (rp-valid-termp)
     )
    t)

  (defun rp-meta-fnc (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :fnc))

  (defun rp-meta-trig-fnc (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :trig-fnc))

  (defun rp-meta-dont-rw (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :dont-rw))

  (defun rp-meta-syntax-verified (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :valid-syntax))

  #|(defun rp-meta-rule-syntaxp (term)
  "Returned term from meta rule functin should meet this syntax."
  (rp-valid-termp term))||#

  (defun rp-meta-rule-rec-p (rule state)
    (declare (xargs :guard t
                    :stobjs (state)))
    (and (weak-rp-meta-rule-rec-p rule)
         (symbolp (rp-meta-fnc rule))
         (acl2::logicp (rp-meta-fnc rule) (w state))
         (symbolp (rp-meta-trig-fnc rule))
         (booleanp (rp-meta-dont-rw rule))
         (booleanp (rp-meta-syntax-verified rule))))

  (defun weak-rp-meta-rule-recs-p (xs)
    (declare (xargs :guard t))
    (if (atom xs)
        (eq xs nil)
      (and (weak-rp-meta-rule-rec-p (car xs))
           (weak-rp-meta-rule-recs-p (cdr xs)))))

  (defun rp-meta-rule-recs-p (rules state)
    (declare (xargs :guard t
                    :stobjs (state)))
    (if (atom rules)
        (eq rules nil)
      (and (rp-meta-rule-rec-p (car rules) state)
           (rp-meta-rule-recs-p (cdr rules) state))))

  (in-theory (disable weak-rp-meta-rule-rec-p
                      rp-meta-syntax-verified
                      rp-meta-dont-rw
                      rp-meta-trig-fnc
                      rp-meta-fnc))

  (defund rp-meta-valid-syntaxp (meta-rule term state)
    (declare (xargs :guard (rp-meta-rule-rec-p meta-rule state)
                    :stobjs (state)))
    (b* (((mv error res)
          (magic-ev-fncall (rp-meta-fnc meta-rule)
                           (list term)
                           state
                           t nil)))
      (implies
       (and (not error)
            (acl2::logicp (rp-meta-fnc meta-rule) (w state)))
       (and (if (rp-meta-dont-rw meta-rule)
                (and
                 (natp (mv-nth 1 res))
                 (natp (mv-nth 2 res))
                 (if (rp-meta-syntax-verified meta-rule)
                     (implies (rp-valid-termp term)
                              (rp-valid-termp (mv-nth 0 res)))
                   t))
              (and (if (rp-meta-syntax-verified meta-rule)
                       (implies (rp-valid-termp term)
                                (rp-valid-termp res))
                     t)))))))

  (defun-sk rp-meta-valid-syntaxp-sk (meta-rule state-)
    (declare (xargs :guard (and (STATE-P1 STATE-))
                    :verify-guards nil))
    (forall term
            (rp-meta-valid-syntaxp meta-rule term state-)))

  (defund rp-meta-valid-syntax-listp (meta-rules state)
    (declare (xargs :guard (rp-meta-rule-recs-p meta-rules state)
                    :verify-guards nil
                    :stobjs (state)))
    (if (atom meta-rules)
        (eq meta-rules nil)
      (and (rp-meta-valid-syntaxp-sk (car meta-rules) state)
           (rp-meta-valid-syntax-listp (cdr meta-rules) state))))

  #|(defmacro rp-meta-rulesp (meta-rules &optional (state 'state))
  (declare (xargs :guard t)
  (ignorable state))
  `(and (weak-rp-meta-rule-recs-p ,meta-rules)
  ;;(rp-meta-valid-syntax-listp ,meta-rules ,state)
  ))||#)

(mutual-recursion
 (defun subtermp (term subterm)
   (declare (xargs :guard t))
   (cond ((atom term)
          (equal term subterm))
         ((quotep term)
          (equal term subterm))
         (t
          (or (equal term subterm)
              (equal (car term) subterm)
              (subtermp-lst (cdr term) subterm)))))
 (defun subtermp-lst (lst subterm)
   (if (atom lst)
       nil
     (or (subtermp (car lst) subterm)
         (subtermp-lst (cdr lst) subterm)))))

(encapsulate
  nil

  #|(defun lambda-pairs (keys vals)
  (declare (xargs :guard t))
  (if (or (atom keys)
  (atom vals))
  nil
  (acons (car keys) (car vals)
  (lambda-pairs (cdr keys) (cdr vals)))))||#

  (defun rp-beta-reduce-get-val (key keys vals)
    (declare (xargs :guard t))
    (cond ((atom keys)
           (progn$ (cw "warning binding problem! ~p0 ~%" key)
                   key))
          ((equal key (car keys))
           (if (consp vals) (car vals) key))
          (t (rp-beta-reduce-get-val key (cdr keys)
                                     (if (consp vals) (cdr vals) nil)))))

  (mutual-recursion
   (defun rp-beta-reduce (term keys vals)
     (declare (xargs :guard t))
     (cond ((atom term)
            (rp-beta-reduce-get-val term keys vals))
           ((acl2::fquotep term) term)
           (t (cons-with-hint (car term)
                              (rp-beta-reduce-subterms (cdr term) keys vals)
                              term))))

   (defun rp-beta-reduce-subterms (subterms keys vals)
     (cond ((atom subterms) subterms)
           (t (cons-with-hint (rp-beta-reduce (car subterms) keys vals)
                              (rp-beta-reduce-subterms (cdr subterms) keys vals)
                              subterms)))))

  (defund rp-beta-reduce-main (term)
    (declare (xargs :guard t
                    :guard-hints (("Goal"
                                   :in-theory (e/d (is-lambda) ())))))
    (if (is-lambda term)
        (rp-beta-reduce (caddr (car term)) (cadar term) (cdr term))
      term)))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (consp x)
                   (consp (cdr x)))
              (< (len (evens x))
                 (len x)))))

  (local
   (defthm lemma2
     (implies (and (consp x)
                   )
              (< (len (evens x))
                 (1+ (len x))))))

  (local
   (defthm lemma3
     (IMPLIES (AND (CONSP (CDR L)) (CONSP L))
              (< (LEN (EVENS L)) (+ 1 (LEN (CDR L)))))))

  (defun merge-comperator (l1 l2 acc comperator)
    (declare (xargs :guard (and (true-listp l1)
                                (true-listp l2)
                                (true-listp acc)
                                (symbolp comperator ))
                    :measure (+ (len l1) (len l2))))
    (cond
     ((endp l1)
      (revappend acc l2))
     ((endp l2)
      (revappend acc l1))
     ((apply$ comperator (list (car l1) (car l2)))
      (merge-comperator  (cdr l1)
                         l2
                         (cons (car l1) acc)
                         comperator))
     (t (merge-comperator  l1 (cdr l2)
                           (cons (car l2) acc) comperator))))

  (defun merge-comperator-sort (l comperator)
    (declare (xargs :guard (and (true-listp l)
                                (symbolp comperator))
                    :measure (len l)
                    :verify-guards nil))
    (cond ((endp (cdr l)) l)
          (t (merge-comperator
              (merge-comperator-sort (evens l) comperator)
              (merge-comperator-sort (odds l) comperator)
              nil
              comperator))))

  (local
   (defthm true-listp-of-merge-comprerator
     (implies (and (true-listp l1)
                   (true-listp l2)
                   (true-listp acc))
              (true-listp (merge-comperator l1 l2 acc comperator)))))

  (local
   (defthm true-listp-of-merge-sort
     (implies (true-listp l)
              (true-listp (merge-comperator-sort l comperator)))))

  (verify-guards merge-comperator-sort))



(acl2::defines
 generate-dont-rw-from-term
 :verify-guards nil
 :prepwork
 ((local
   (in-theory (disable logapp natp))))
 (define generate-dont-rw-from-term (term)
   :returns (mv (dont-rw natp)
                (size natp))
   (cond ((or (atom term)
              (acl2::fquotep term))
          (mv 1 1))
         ((eq (car term) 'synp)
          (mv 1 1))
         ((eq (car term) 'hide)
          (mv 2 2))
         ;; skip synp and insides of hide.
         (t (b* (((mv rest rest-size)
                  (generate-dont-rw-from-term-lst (cdr term))))
              (mv (logapp 1 0 rest)
                  (1+ rest-size))))))
 (define generate-dont-rw-from-term-lst (lst)
   :returns (mv (dont-rw natp)
                (size natp))
   (if (atom lst)
       (mv 0 0)
     (b* (((mv rest1 rest1-size)
           (generate-dont-rw-from-term (car lst)))
          ((mv rest2 rest2-size)
           (generate-dont-rw-from-term-lst (cdr lst))))
       (mv (logapp rest1-size rest1 rest2)
           (+ rest1-size rest2-size)))))
 ///
 (verify-guards generate-dont-rw-from-term))

(acl2::defines
 cut-dont-rw-with-term
 (define cut-dont-rw-with-term ((dont-rw natp)
                                (term))
   :returns (res natp :hyp (natp dont-rw))
   :measure (acl2-count term)
   :verify-guards nil
   (cond
    ((or (atom term)
         (acl2::fquotep term))
     (progn$ (and (equal (acl2::logcar dont-rw) 0)
                  (hard-error 'cut-dont-rw-with-term
                              "Unexpected dont-rw"
                              nil))
             (acl2::logcdr dont-rw)))
    ((= (acl2::logcar dont-rw) 1)
     (acl2::logcdr dont-rw))
    (t (cut-dont-rw-with-term-lst (acl2::logcdr dont-rw) (cdr term)))))
 (define cut-dont-rw-with-term-lst ((dont-rw natp)
                                    (lst))
   :measure (acl2-count lst)
   :returns (res natp :hyp (natp dont-rw))
   (if (atom lst)
       dont-rw
     (cut-dont-rw-with-term-lst
      (cut-dont-rw-with-term dont-rw (car lst))
      (cdr lst))))
 ///
 (verify-guards cut-dont-rw-with-term))

(acl2::defines
 cut-dont-rw-with-term-2
  :prepwork
 ((local
   (in-theory (disable logapp ))))
 (define cut-dont-rw-with-term-2 ((dont-rw natp)
                                (term))
   :returns (mv (res natp :hyp (natp dont-rw))
                (cut natp :hyp (natp dont-rw))
                (cut-size natp :hyp (natp dont-rw)))
   :measure (acl2-count term)
   :verify-guards nil
   (cond
    ((or (atom term)
         (acl2::fquotep term))
     (progn$
      (and (equal (acl2::logcar dont-rw) 0)
           (hard-error 'cut-dont-rw-with-term
                       "Unexpected dont-rw"
                       nil))
      (mv (acl2::logcdr dont-rw)
          (acl2::logcar dont-rw)
          1)))
    ((= (acl2::logcar dont-rw) 1)
     (mv (acl2::logcdr dont-rw) (acl2::logcar dont-rw) 1))
    (t (b* (((mv dont-rw cut-dont-rw cut-dont-rw-size)
             (cut-dont-rw-with-term-lst-2 (acl2::logcdr dont-rw) (cdr term))))
         (mv dont-rw
             (logapp 1 0 cut-dont-rw)
             (1+ cut-dont-rw-size))))))
 
 (define cut-dont-rw-with-term-lst-2 ((dont-rw natp)
                                    (lst))
   :measure (acl2-count lst)
   :returns (mv (res natp :hyp (natp dont-rw))
                (cut natp :hyp (natp dont-rw))
                (cut-size natp :hyp (natp dont-rw)))
   (if (atom lst)
       (mv dont-rw 0 0)
     (b* (((mv dont-rw cut1 cut1-size)
           (cut-dont-rw-with-term-2 dont-rw (car lst)))
          ((mv dont-rw cut2 cut2-size)
           (cut-dont-rw-with-term-lst-2
            dont-rw (cdr lst))))
       (mv dont-rw
           (logapp cut1-size cut1 cut2)
           (+ cut1-size cut2-size)))))
 ///
 (local
  (defthm natp-implies-integerp
    (implies (natp x)
             (and (integerp x)
                  (acl2-numberp x)))))
 
 (verify-guards cut-dont-rw-with-term-2
   :hints (("Goal"
            :in-theory (e/d () ())))))


;; (generate-dont-rw-from-term '(f1 a b (f2 '3 (f4 b c "g" (f2 a)))))

;; (cut-dont-rw-with-term #b10010111010110 '(f1 (f5 v) b (f2 '3 (f4 b c "g" (f2
;;                                                                           a)))))
;; (cut-dont-rw-with-term-2 #b10010111010110 '(f1 (f5 v) b (f2 '3 (f4 b c "g" (f2 a)))))

(defmacro mv-nth$ (pos term total)
  `(b* (((mv ,@(sas '?x 0 total))
         ,term))
     ,(sa 'x pos)))


(define dont-rw-to-binary-string (dont-rw)
  ;; :prepwork
  ;; ((local
  ;;   (include-book "arithmetic-5/top" :dir :system)))
  :returns (res stringp :hyp (integerp dont-rw))
  :verify-guards nil
  (cond ((not dont-rw)
         nil)
        ((= (nfix dont-rw) 0)
         "")
        (t (str::cat
            (str::intstr (acl2::logcar dont-rw))
            (dont-rw-to-binary-string (acl2::logcdr (nfix dont-rw))))))
  ///
  (verify-guards dont-rw-to-binary-string)) 



(acl2::defines
 dont-rw-consistentp
 (define dont-rw-consistentp-aux ((dont-rw natp)
                                  (term))
   :measure (acl2-count term)
   :returns (mv (res-dont-rw natp :hyp (natp dont-rw))
                (result booleanp))
   :verify-guards nil
   (b* ((bit0 (acl2::logcar dont-rw)))
     (cond ((equal bit0 1)
            (mv (acl2::logcdr dont-rw)
                t))
           ((or (atom term)
                (acl2::fquotep term))
            (mv (acl2::logcdr dont-rw)
                nil)) ;; bit0 should be 1 so test fails
           (t
            (dont-rw-consistentp-aux-lst (acl2::logcdr dont-rw)
                                         (cdr term))))))
 (define dont-rw-consistentp-aux-lst ((dont-rw natp)
                                      (lst))
   :measure (acl2-count lst)
   :returns (mv (res-dont-rw natp :hyp (natp dont-rw))
                (result booleanp))
   (if (atom lst)
       (mv dont-rw t)
     (b* (((mv dont-rw car-res)
           (dont-rw-consistentp-aux dont-rw
                                    (car lst)))
          ((unless car-res)
           (mv dont-rw nil)))
       (dont-rw-consistentp-aux-lst dont-rw
                                    (cdr lst)))))
 ///
 (verify-guards dont-rw-consistentp-aux))
   


(define dont-rw-consistentp ((dont-rw natp)
                             (term))
  (b* (((mv dont-rw res) (dont-rw-consistentp-aux dont-rw term)))
    (and (equal dont-rw 0)
         res)))


#|(let ((term '(f1 a b (f2 '3 (f4 b c "g" (f2 a))))))
  (dont-rw-consistentp (mv-nth$ 0 (generate-dont-rw-from-term term) 2) term))||#
