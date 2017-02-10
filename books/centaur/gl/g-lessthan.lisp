; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))

(defun g-<-of-numbers (a b)
  (declare (xargs :guard (and (general-numberp a)
                              (general-numberp b))))
  (b* (((mv arn ard ain aid)
        (general-number-components a))
       ((mv brn brd bin bid)
        (general-number-components b)))

    (if (and (equal ard brd)
             (equal aid bid))
        (mk-g-boolean
         (bfr-ite (bfr-=-uu ard nil)
                  (bfr-and (bfr-not (bfr-=-uu aid nil))
                           (bfr-<-ss ain bin))
                  (bfr-or (bfr-<-ss arn brn)
                          (bfr-and (bfr-not (bfr-=-uu aid nil))
                                   (bfr-<-ss ain bin)
                                   (bfr-=-ss arn brn)))))
      (g-apply '< (gl-list a b)))))

(defthm deps-of-g-<-of-numbers
  (implies (and (not (gobj-depends-on k p a))
                (not (gobj-depends-on k p b))
                (general-numberp a)
                (general-numberp b))
           (not (gobj-depends-on k p (g-<-of-numbers a b)))))

(in-theory (disable (g-<-of-numbers)))

(local
 (encapsulate nil
   (local
    (defthm rationalp-complex
      (equal (rationalp (complex a b))
             (equal (rfix b) 0))
      :hints (("goal" :use ((:instance
                             (:theorem (implies (rationalp x)
                                                (equal (imagpart x) 0)))
                             (x (complex a b))))))))


   (defthm realpart-of-complex
     (equal (realpart (complex a b))
            (rfix a))
     :hints (("goal" :cases ((rationalp b)))))

   (defthm imagpart-of-complex
     (equal (imagpart (complex a b))
            (rfix b))
     :hints (("goal" :cases ((rationalp a)))))


   (defthm complex-<-1
     (equal (< (complex a b) c)
            (or (< (rfix a) (realpart c))
                (and (equal (rfix a) (realpart c))
                     (< (rfix b) (imagpart c)))))
     :hints (("goal" :use ((:instance completion-of-<
                            (x (complex a b)) (y c))))))


   (defthm complex-<-2
     (equal (< a (complex b c))
            (or (< (realpart a) (rfix b))
                (and (equal (realpart a) (rfix b))
                     (< (imagpart a) (rfix c)))))
     :hints (("goal" :use ((:instance completion-of-<
                            (x a) (y (complex b c)))))))))

(local
 (progn
   ;; (defthm gobjectp-g-<-of-numbers
   ;;   (implies (and (gobjectp a)
   ;;                 (general-numberp a)
   ;;                 (gobjectp b)
   ;;                 (general-numberp b))
   ;;            (gobjectp (g-<-of-numbers a b))))

   (local (include-book "arithmetic/top-with-meta" :dir :system))

   (defthm g-<-of-numbers-correct
     (implies (and (general-numberp a)
                   (general-numberp b))
              (equal (eval-g-base (g-<-of-numbers a b) env)
                     (< (eval-g-base a env)
                        (eval-g-base b env))))
     :hints (("goal" :do-not-induct t
              :in-theory (e/d* ((:ruleset general-object-possibilities))))))))

(in-theory (disable g-<-of-numbers))

(def-g-binary-op <
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (gret (g-<-of-numbers x-num y-num))))

;; (def-gobjectp-thm <
;; :hints `(("Goal" :in-theory (e/d* (booleanp-gobjectp
;;                                    boolean-listp-bfr-listp
;;                                    gobjectp-of-atomic-constants)
;;                                   ((:definition ,gfn)
;;                                    number-to-components
;;                                    general-concretep-def
;;                                    gobj-fix-when-not-gobjectp
;;                                    gobj-fix-when-gobjectp
;;                                    booleanp-gobjectp
;;                                    (:ruleset gl-wrong-tag-rewrites)
;;                                    (:rules-of-class :type-prescription :here)))
;;           :induct (,gfn x y hyp clk)
;;           :expand ((,gfn x y hyp clk)))))

(verify-g-guards
 < :hints `(("Goal" :in-theory (disable* ,gfn general-concretep-def))))

(def-gobj-dependency-thm <
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))


(def-g-correct-thm < eval-g-base
  :hints `(("Goal" :in-theory (e/d* ((:ruleset general-object-possibilities)
                                     not-general-numberp-not-acl2-numberp)
                                    ((:definition ,gfn)
                                     (:rules-of-class :type-prescription :here)
                                     number-to-components
                                     general-concretep-def
                                     components-to-number
                                     eval-g-base-non-cons
                                     acl2::/r-when-abs-numerator=1
                                     default-unary-/
                                     default-car default-cdr
                                     hons-assoc-equal))
            :induct ,gcall
            :expand (,gcall))))
