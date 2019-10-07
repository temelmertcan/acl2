; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "../bits-sbits")

(local
 (in-theory (enable bits-sbits-no-syntaxp)))

(local
 (in-theory (disable 4vec-zero-ext-is-bits
                     logapp
                     ash
                     natp)))

(encapsulate
  nil

  ;; Functions for bits-of-meta-fn

  (define is-bits-of-sbits (term)
    (case-match term
      (('bits sbits
              ('quote &)
              ('quote &))
       (b* ((sbits (rp::ex-from-rp sbits)))
         (case-match sbits
           (('sbits ('quote &) ('quote &) & &)
            t)
           (&
            nil))))
      (& nil))
    ///
    (defthm is-bits-of-sbits-implies
      (implies (is-bits-of-sbits term)
               (case-match term
                 (('bits sbits
                         ('quote &)
                         ('quote &)
                         )
                  (b* ((sbits (rp::ex-from-rp sbits)))
                    (case-match sbits
                      (('sbits ('quote &) ('quote &) & &)
                       t)
                      (&
                       nil))))
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-bits-of-sbits-loose (term)
    (case-match term
      (('bits ('sbits & & & &) & & )
       t)
      (& nil))
    ///
    (defthm is-bits-of-sbits-loose-implies
      (implies (is-bits-of-sbits-loose term)
               (case-match term
                 (('bits ('sbits & & & &) & & )
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-bits-of-rsh (term)
  ;;;;; change to accomodate rp terms as well!
    (case-match term
      (('bits ('4vec-rsh ('quote &) &) ('quote &) ('quote &) )
       t)
      (& nil))
    ///
    (defthm is-bits-of-rsh-implies
      (implies (is-bits-of-rsh term)
               (case-match term
                 (('bits ('4vec-rsh ('quote &) &) ('quote &) ('quote &) )
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-bits-of-concat (term)
  ;;;;; change to accomodate rp terms as well!
    (case-match term
      (('bits ('4vec-concat$ ('quote &) & &) ('quote &) ('quote &) )
       t)
      (& nil))
    ///
    (defthm is-bits-of-concat-implies
      (implies (is-bits-of-concat term)
               (case-match term
                 (('bits ('4vec-concat$ ('quote &) & &) ('quote &) ('quote &) )
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-bits-of-bits (term)
    (case-match term
      (('bits ('bits & ('quote &) ('quote &)) ('quote &) ('quote &) )
       t)
      (& nil))
    ///
    (defthm is-bits-of-bits-implies
      (implies (is-bits-of-bits term)
               (case-match term
                 (('bits ('bits & ('quote &) ('quote &)) ('quote &) ('quote &) )
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-bits-0-1-of-a-bitp (term)
    (case-match term
      (('bits ('rp ''bitp &) ''0 ''1)
       t)
      (& nil))
    ///
    (defthm is-bits-0-1-of-a-bitp-implies
      (implies (is-bits-0-1-of-a-bitp term)
               (case-match term
                 (('bits ('rp ''bitp &) ''0 ''1 )
                  t)
                 (& nil)) )
      :rule-classes :forward-chaining))

  (define is-bits-of-bitand/or/xor (term)
    (case-match term
      (('bits ('4vec-bitand & &) ('quote s) ('quote w))
       (and (natp s)
            (natp w)))
      (('bits ('4vec-bitor & &) ('quote s) ('quote w))
       (and (natp s)
            (natp w)))
      (('bits ('sv::4vec-bitxor & &) ('quote s) ('quote w))
       (and (natp s)
            (natp w)))
      (& nil))
    ///
    (defthm is-bits-of-bitand/or/xor-implies
      (implies (is-bits-of-bitand/or/xor term)
               (case-match term
                 (('bits ('4vec-bitand & &) ('quote s) ('quote w))
                  (and (natp s)
                       (natp w)))
                 (('bits ('4vec-bitor & &) ('quote s) ('quote w))
                  (and (natp s)
                       (natp w)))
                 (('bits ('sv::4vec-bitxor & &) ('quote s) ('quote w))
                  (and (natp s)
                       (natp w)))
                 (& nil)) )
      :rule-classes :forward-chaining))

  (defun bits-of-meta-fn (term)
    (declare (xargs :mode :program))
    (cond
     ((is-bits-of-sbits term)
      (b* ((start (car (cdr (car (cddr term)))))
           (size (car (cdr (car (cddr (cdr term))))))
           (sbits (car (cdr term)))
           (sbits (rp::ex-from-rp sbits))
           (s-start (car (cdr (car (cdr sbits)))))
           (s-size (car (cdr (car (cdr (cdr sbits))))))
           (val (car (cdr (cdr (cdr sbits)))))
           (old-val (car (cdr (cdr (cdr (cdr sbits)))))))
        (cond
         ((not (and (natp start)
                    (natp size)
                    (natp s-start)
                    (natp s-size)))
          (progn$
           (cw "unexpected instances of bits of sbits ~%")
           (hard-error 'bits-of-meta-fn "error" nil)
           (mv term 1 1)))
         ((or (<= (+ start size) s-start) ;;case5
              (<= (+ s-start s-size) start))
          (bits-of-meta-fn `(bits ,old-val ',start ',size)))
         ((and (<= (+ start size) ;;case4
                   (+ s-start s-size))
               (<= s-start start))
          (bits-of-meta-fn `(bits ,val ',(- start s-start) ',size )))
         ((and (< start s-start) ;;case 3
               (< s-start (+ start size))
               (<= (+ start size)
                   (+ s-start s-size)))
          (b* (((mv rest-term rest-dontrw rest-dontrw-size)
                (bits-of-meta-fn `(bits ,old-val ',start ',(- s-start start) )))
               ((mv rest-term2 rest-dontrw2 rest-dontrw2-size)
                (bits-of-meta-fn `(bits ,val '0 ',(+ start size (- s-start)) ))))
            (mv `(4vec-concat$ ',(- s-start start)
                               ,rest-term
                               ,rest-term2)
                (logapp 2 #b10
                        (logapp rest-dontrw-size
                                rest-dontrw
                                rest-dontrw2))
                (+ 2 rest-dontrw-size
                   rest-dontrw2-size)
                #|`(nil t
                ,rest-dontrw
                ,rest-dontrw2)||#)))
         ((and (<= s-start start) ;;case 2
               (< start (+ s-start s-size))
               (< (+ s-start s-size)
                  (+ start size)))
          (b* (((mv rest-term rest-dontrw rest-dontrw-size)
                (bits-of-meta-fn `(bits ,val
                                        ',(- start s-start)
                                        ',(+ s-size s-start (- start))
                                        )))
               ((mv rest-term2 rest-dontrw2 rest-dontrw2-size)
                (bits-of-meta-fn `(bits ,old-val
                                        ',(+ s-start s-size)
                                        ',(+ size start (- (+ s-start s-size)))))))
            (mv `(4vec-concat$
                  ',(+ s-size s-start (- start))
                  ,rest-term
                  ,rest-term2)
                (logapp 2 #b10
                        (logapp rest-dontrw-size
                                rest-dontrw
                                rest-dontrw2))
                (+ 2 rest-dontrw-size
                   rest-dontrw2-size)
                #|`(nil
                t
                ,rest-dontrw
                ,rest-dontrw2)||#)))

         ((and (< start s-start) ;;case 1
               (< (+ s-start s-size)
                  (+ start size)))
          (b* (((mv rest-term2 rest-dont-rw2 rest-dont-rw2-size)
                (bits-of-meta-fn `(bits ,old-val ',start ',(- s-start start) )))
               ((mv rest-term3 rest-dont-rw3 rest-dont-rw3-size)
                (bits-of-meta-fn `(bits ,val '0 ',s-size )))
               ((mv rest-term4 rest-dont-rw4 rest-dont-rw4-size)
                (bits-of-meta-fn `(bits ,old-val
                                        ',(+ s-start s-size)
                                        ',(- (+ start size) (+ s-start s-size))
                                        ))))
            (mv `(4vec-concat$ ',(- s-start start)
                               ,rest-term2
                               (4vec-concat$ ',s-size ,rest-term3 ,rest-term4))
                (logapp 2 #b10
                        (logapp rest-dont-rw2-size
                                rest-dont-rw2
                                (logapp 2 #b10
                                        (logapp rest-dont-rw3-size
                                                rest-dont-rw3
                                                rest-dont-rw4))))
                (+ 4 rest-dont-rw2-size
                   rest-dont-rw3-size
                   rest-dont-rw4-size)
                #|`(nil t
                ,rest-dont-rw2
                (nil t ,rest-dont-rw3 ,rest-dont-rw4))||#)))
         (t
          (progn$
           (cw "unexpected instance of bits of sbits ~%")
           (hard-error 'bits-of-meta-fn "error" nil)
           (mv term 1 1))))))
     ((is-bits-of-rsh term)
      (let ((start (car (cdr (car (cddr term)))))
            (size (car (cdr (car (cdr (cddr term))))))
            (rsh-size (car (cdr (car (cdr (car (cdr term)))))))
            (val (car (cdr (cdr (car (cdr term)))))))

        (if (and (natp start)
                 (natp size)
                 (natp rsh-size))
            (bits-of-meta-fn `(bits ,val ',(+ start rsh-size) ',size ))
          (progn$
           (cw "unexpected instance of bits of rsh ~%")
           (hard-error 'bits-of-meta-fn "error" nil)
           (mv term 1 1)))))

     ((is-bits-of-concat term)
      (let ((start (car (cdr (car (cddr term)))))
            (size (car (cdr (car (cddr (cdr term))))))
            (c-size (car (cdr (car (cdr (car (cdr term)))))))
            (term1 (car (cdr (cdr (car (cdr term))))))
            (term2 (car (cdr (cdr (cdr (car (cdr term))))))))
        (cond ((not (and (natp start)
                         (natp size)
                         (natp c-size)))
               (progn$
                (cw "unexpected instance of bits of concat Not natps ~%")
                (hard-error 'bits-of-meta-fn "error" nil)
                (mv term 1 1)))
              ((<= c-size start) ;;case 2
               (bits-of-meta-fn `(bits ,term2 ',(- start c-size) ',size )))
              ((and (< start c-size) ;; case 3
                    (< c-size (+ start size)))
               (b* (((mv rest-term1 rest-dontrw rest-dontrw-size)
                     (bits-of-meta-fn `(bits ,term1
                                             ',start ',(- c-size start)
                                             )))
                    ((mv rest-term2 rest-dontrw2 rest-dontrw2-size)
                     (bits-of-meta-fn `(bits ,term2
                                             '0 ',(- size (- c-size start))
                                             ))))
                 (mv `(4vec-concat$ ',(- c-size start)
                                    ,rest-term1
                                    ,rest-term2)
                     (logapp 2 #b10
                             (logapp rest-dontrw-size
                                     rest-dontrw
                                     rest-dontrw2))
                     (+ 2 rest-dontrw-size
                        rest-dontrw2-size)
                     #|`(nil t
                     ,rest-dontrw
                     ,rest-dontrw2)||#)))
              ((<= (+ start size) c-size)
               (bits-of-meta-fn `(bits ,term1 ',start ',size )))
              (t
               (progn$
                (cw "unexpected instance of bits of concats ~%")
                (hard-error 'bits-of-meta-fn "error" nil)
                (mv term 1 1))))))
     ((is-bits-0-1-of-a-bitp term)
      (bits-of-meta-fn (cadr term)))
     ((is-bits-of-bits term)
      (case-match term
        (('bits ('bits x ('quote start2) ('quote size2)) ('quote start1) ('quote size1))
         (cond ((not (and (natp start1)
                          (natp start2)
                          (natp size1)
                          (natp size2)))
                (progn$
                 (cw "unexpected instance of bits of concat Not natps ~%")
                 (hard-error 'bits-of-meta-fn "error" nil)
                 (mv term 1 1)))
               ((< start1 size2)
                (bits-of-meta-fn  `(bits ,x
                                         ',(+ start1 start2)
                                         ',(min size1 (- size2 start1))
                                         )))
               (t (mv ''0 1 1))))
        (& (mv term 1 1))))
     ((is-bits-of-bitand/or/xor term)
      (case-match term
        (('bits (fnc term1 term2) start size)
         (b* (((mv rest1 dont-rw1 dont-rw1-size)
               (bits-of-meta-fn `(bits ,term1 ,start ,size)))
              ((mv rest2 dont-rw2 dont-rw2-size)
               (bits-of-meta-fn `(bits ,term2 ,start ,size))))
           (mv `(,fnc ,rest1 ,rest2)
               (logapp 1 0
                       (logapp dont-rw1-size
                               dont-rw1
                               dont-rw2))
               (+ 1 dont-rw1-size dont-rw2-size)
               #|`(nil ,dont-rw1 ,dont-rw2)||#)))
        (& (mv term 1 1))))
     (t
      (case-match term
        (('bits & ('quote &) ('quote &))
         (mv term #b1110 4
             #|`(nil t t t)||#
             ))
        (& (mv term 1 1)))))))

(encapsulate
  nil

  (local
   (defthm m-lemma1
     (implies (or (IS-BITS-OF-CONCAT TERM)
                  (IS-BITS-OF-RSH term))
              (and (O< (+ 8 (CONS-COUNT (CADDR (CADR TERM))))
                       (CONS-COUNT TERM))
                   (O< (+ 8 (CONS-COUNT (CADDDR (CADR TERM))))
                       (CONS-COUNT TERM))))

     :hints (("Goal"
              :in-theory (e/d (CONS-COUNT IS-BITS-OF-CONCAT
                                          IS-BITS-OF-RSH) ())))))

  (verify-termination
    bits-of-meta-fn
    (declare
     (xargs
      :measure (rp::cons-count term)
      :hints (("goal"
               :in-theory
               (e/d (is-bits-of-sbits
                     rp::measure-lemmas)
                    ((:definition not)
                     (:e tau-system)
                     (:rewrite rp::measure-lemma1-2)
                     (:definition acl2::apply$-badgep)
                     (:definition member-equal)
                     (:rewrite rp::equality-measure-lemma1)
                     (:definition subsetp-equal)
                     (:definition acl2-number-listp)
                     (:definition rational-listp)
                     (:definition nat-listp)
                     (:rewrite rationalp-implies-acl2-numberp)
                     (:rewrite rp::equality-measure-lemma7)
                     (:rewrite default-<-1)
                     (:rewrite default-+-2)
                     (:definition acl2::weak-apply$-badge-p)
                     (:rewrite rp::equality-measure-lemma8)
                     (:rewrite rp::measure-lemma1)
                     (:rewrite default-cdr)
                     (:rewrite default-car)
                     (:rewrite default-<-2)
                     (:rewrite default-+-1)
                     (:rewrite rp::equality-measure-lemma6)
                     (:rewrite rp::sum-with-positive-lemma1)
                     (:rewrite rp::measure-lemma6-5)
                     (:rewrite rp::equality-measure-lemma5)
                     (:definition posp)
                     (:rewrite rp::measure-lemma7-2)
                     (:definition natp))))))))

  (defthm natp-dont-rw-bits-of-meta-fn
    (and (natp (mv-nth 1 (bits-of-meta-fn x)))
         (natp (mv-nth 2 (bits-of-meta-fn x))))
    :hints (("goal"
             :in-theory (e/d ()
                             (associativity-of-+
                              acl2::commutativity-2-of-+
                              commutativity-of-+
                              acl2::distributivity-of-minus-over-+
                              (:elim car-cdr-elim))))))

  (verify-guards bits-of-meta-fn))

(encapsulate
  nil
  (define is-concat$-of-concat$ (term)
    (case-match term
      (('4vec-concat$ ('quote &)
                      ('4vec-concat$ ('quote &) & &)
                      &)
       t)
      (& nil))
    ///
    (defthm is-concat$-of-concat$-implies
      (implies (is-concat$-of-concat$ term)
               (case-match term
                 (('4vec-concat$ ('quote &)
                                 ('4vec-concat$ ('quote &) & &)
                                 &)
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-concat-of-concat$ (term)
    (case-match term
      (('4vec-concat ('quote &)
                     ('4vec-concat$ ('quote &) & &)
                     &)
       t)
      (& nil))
    ///
    (defthm is-concat-of-concat$-implies
      (implies (is-concat-of-concat$ term)
               (case-match term
                 (('4vec-concat ('quote &)
                                ('4vec-concat$ ('quote &) & &)
                                &)
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-concat (term)
    (case-match term
      (('4vec-concat ('quote &)
                     &
                     &)
       t)
      (& nil))
    ///
    (defthm is-concat-implies
      (implies (is-concat term)
               (case-match term
                 (('4vec-concat ('quote &)
                                &
                                &)
                  t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (define is-concat$ (term)
    (case-match term
      (('4vec-concat$ ('quote &) & &) t)
      (& nil))
    ///
    (defthm is-concat$-implies
      (implies (is-concat$ term)
               (case-match term
                 (('4vec-concat$ ('quote &) & &) t)
                 (& nil)))
      :rule-classes :forward-chaining))

  (defun concat-of-meta-fn (term limit)
    (declare (xargs :measure (nfix limit)
                    :verify-guards nil
                    :guard (natp limit)))
    (if (zp limit)
        (mv term 1 1)
      (cond ((or (is-concat-of-concat$ term)
                 (is-concat$-of-concat$ term))
             (case-match term
               ((& ('quote size1)
                   ('4vec-concat$ ('quote size2) term1 term2)
                   term3)
                (cond
                 ((not (and (natp size1)
                            (natp size2)))
                  (mv term 1 1))
                 ((<= size1 size2)
                  (concat-of-meta-fn `(4vec-concat ',size1 ,term1 ,term3)
                                     (1- limit)))
                 (t
                  (b* (((mv rest rest-dontrw rest-dontrw-size)
                        (concat-of-meta-fn `(4vec-concat ',(- size1 size2) ,term2
                                                         ,term3)
                                           (1- limit))))
                    (mv `(4vec-concat$ ',size2 ,term1
                                       ,rest)
                        (logapp 3 #b110
                                rest-dontrw)
                        (+ 3 rest-dontrw-size)
                        #|`(nil t t ,rest-dontrw)||#)))))
               (& (mv term 1 1))))
            ((is-concat term)
             (case-match term
               (('4vec-concat ('quote size1) term1 term2)

                (cond ((equal size1 0)
                       (mv `(sv::4vec-fix$inline ,term2) #b10 2 #|`(nil t)||#))
                      ((and (equal size1 1)
                            (equal term2 ''0))
                       (mv `(bits ,term1 '0 '1 )
                           #b1110 4
                           #|`(nil t t t)||#))
                      (t
                       (mv
                        `(4vec-concat$ ',size1
                                       (bits ,term1 '0 ',size1 )
                                       ,term2)
                        #b1111010 7
                        #|`(nil t (nil t t t) t)||#))))
               (& (mv term 1 1))))
            ((is-concat$ term)
             (mv term #b1110 4 #|`(nil t t t)||#))
            (t
             (mv term 1 1)))))


  
   (defthm natp-dont-rw-concat-of-meta-fn
     (and (natp  (mv-nth 1 (concat-of-meta-fn term limit)))
          (natp  (mv-nth 2 (concat-of-meta-fn term limit)))))

  (verify-guards concat-of-meta-fn)

  (defun concat-of-meta-fn-main (term)
    (concat-of-meta-fn term (expt 2 50)))

  (defund concat-of-meta-fn-main2 (term)
    (concat-of-meta-fn term (expt 2 50)))

  (defthm concat-of-meta-fn-main2-isconcat-of-meta-fn-main
    (equal (concat-of-meta-fn-main2 term)
           (concat-of-meta-fn-main term))
    :hints (("Goal"
             :in-theory (e/d (concat-of-meta-fn-main2) ())))))

(defconst *bits-of-meta-fnc-list*
  '((bits . 3)
    (sbits . 4)
    (4vec-concat . 3)
    (4vec-rsh . 2)
    (4vec-concat$ . 3)
    (sv::4vec-fix$inline . 1)
    (bitp . 1)
    (bits-of-meta-fn . 1)
    (concat-of-meta-fn-main . 1)
    (concat-of-meta-fn-main2 . 1)
    (concat-of-meta-fn . 2)))

(rp::def-formula-checks-default-evl rp::rp-evl
                                    (strip-cars rp::*small-evl-fncs*))

(encapsulate
  nil
  (local
   (in-theory (disable 4VEC-ZERO-EXT-IS-4VEC-CONCAT
                       sv::4VEC-P-OF-4VEC-CONCAT
                       4VEC-PART-SELECT-IS-BITS
                       bits
                       BITS-OF-META-FN
                       4VEC-PART-INSTALL-IS-SBITS
                       CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$
                       (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
                       (:REWRITE COMMUTATIVITY-OF-+)
                       (:REWRITE ACL2::DISTRIBUTIVITY-OF-MINUS-OVER-+)
                       sbits)))

  (rp::def-formula-checks bits-of-formula-checks
                          (bits sbits 4vec-concat
                                4vec-rsh
                                sv::4vec-bitxor
                                sv::4vec-bitand
                                sv::4vec-bitor
                                4vec-concat$
                                sv::4vec-fix$inline
                                bitp bits-of-meta-fn)))

(encapsulate
  nil
  (local
   (in-theory (disable 4VEC-ZERO-EXT-IS-4VEC-CONCAT
                       sv::4VEC-P-OF-4VEC-CONCAT
                       4VEC-PART-SELECT-IS-BITS
                       bits
                       BITS-OF-META-FN
                       4VEC-PART-INSTALL-IS-SBITS
                       CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$
                       (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
                       (:REWRITE COMMUTATIVITY-OF-+)
                       (:REWRITE ACL2::DISTRIBUTIVITY-OF-MINUS-OVER-+)
                       sbits)))

  (rp::def-formula-checks concat-of-formula-checks
                          (bits sbits 4vec-concat
                                4vec-rsh
                                4vec-concat$
                                sv::4vec-fix$inline
                                bitp
                                concat-of-meta-fn-main
                                concat-of-meta-fn
                                )))

(encapsulate
  nil

  (local
   (defthm eval-of-concat-of-meta-fn
     (implies (and (rp-evl-meta-extract-global-facts)
                   (concat-of-formula-checks state))
              (equal (rp::rp-evl (mv-nth 0 (concat-of-meta-fn term limit)) a)
                     (rp::rp-evl term a)))
     :hints (("Goal"
              :in-theory (e/d (rp-evl-of-fncall-args) ())))))

  (local
   (defthm pseudo-termp2-of-concat-of-meta-fn-lemma1
     (IMPLIES (AND (NOT (ZP LIMIT))
                   (NOT (IS-CONCAT-OF-CONCAT$ TERM))
                   (NOT (IS-CONCAT$-OF-CONCAT$ TERM))
                   (IS-CONCAT TERM)
                   (EQUAL (CADR (CADR TERM)) 0)
                   (TRUE-LISTP TERM)
                   (RP::PSEUDO-TERM-LISTP2 (CDDR TERM)))
              (RP::PSEUDO-TERMP2 (CADDDR TERM)))
     :hints (("Goal"
              :in-theory (e/d () ())))))

  (local
   (defthm pseudo-termp2-of-concat-of-meta-fn-lemma2
     (IMPLIES (AND (NOT (ZP LIMIT))
                   (NOT (IS-CONCAT-OF-CONCAT$ TERM))
                   (NOT (IS-CONCAT$-OF-CONCAT$ TERM))
                   (IS-CONCAT TERM)
                   (not (EQUAL (CADR (CADR TERM)) 0))
                   (TRUE-LISTP TERM)
                   (RP::PSEUDO-TERM-LISTP2 (CDDR TERM)))
              (RP::PSEUDO-TERMP2 (CADDDR TERM)))
     :hints (("Goal"
              :in-theory (e/d () ())))))

  (local
   (defthm pseudo-termp2-of-concat-of-meta-fn-lemma3
     (IMPLIES (and (or (RP::PSEUDO-TERMP2 term))
                   (or (IS-CONCAT-OF-CONCAT$ TERM)
                       (IS-CONCAT$-OF-CONCAT$ TERM)))
              (and (RP::PSEUDO-TERMP2 (CADDDR (CADDR TERM)))))
     :hints (("Goal"
              :in-theory (e/d (IS-CONCAT-OF-CONCAT$
                               IS-CONCAT$-OF-CONCAT$) ())))))

  (local
   (defthm pseudo-termp2-of-concat-of-meta-fn
     (implies (rp::pseudo-termp2 term)
              (rp::pseudo-termp2 (mv-nth 0 (concat-of-meta-fn term limit))))
     :otf-flg t
     :hints (("goal"
              :induct (concat-of-meta-fn term limit)
              :do-not-induct t
              :in-theory (e/d ()
                              ((:definition not)
                               (:rewrite associativity-of-+)
                               (:rewrite acl2::commutativity-2-of-+)
                               (:rewrite commutativity-of-+)
                               (:definition natp)
                               (:definition true-listp)))))))

  (local
   (defthm rp-syntaxp-of-concat-of-meta-fn-lemma1
     (implies (and (or (IS-CONCAT-OF-CONCAT$ TERM)
                       (IS-CONCAT$-OF-CONCAT$ TERM))
                   (RP::RP-SYNTAXP term))
              (RP::RP-SYNTAXP (CADDDR (CADDR TERM))))
     :hints (("Goal"
              :in-theory (e/d (IS-CONCAT-OF-CONCAT$
                               IS-CONCAT$-OF-CONCAT$) ())))))

  (local
   (defthm rp-syntaxp-of-concat-of-meta-fn
     (implies (rp::rp-syntaxp term)
              (rp::rp-syntaxp (mv-nth 0 (concat-of-meta-fn term limit))))
     :hints (("Goal"
              :do-not-induct t
              :induct (concat-of-meta-fn term limit)
              :in-theory (e/d () ())))))

  (local
   (defthm all-falist-consistent-concat-of-meta-fn-lemma1
     (implies (and (or (IS-CONCAT-OF-CONCAT$ TERM)
                       (IS-CONCAT$-OF-CONCAT$ TERM))
                   (RP::ALL-FALIST-CONSISTENT term))
              (RP::ALL-FALIST-CONSISTENT (CADDDR (CADDR TERM))))
     :hints (("Goal"
              :in-theory (e/d (IS-CONCAT-OF-CONCAT$
                               IS-CONCAT$-OF-CONCAT$) ())))))

  (local
   (defthm all-falist-consistent-concat-of-meta-fn
     (implies (and (rp::all-falist-consistent term))
              (rp::all-falist-consistent
               (mv-nth 0 (concat-of-meta-fn term limit))))
     :hints (("Goal"
              :do-not-induct t
              :induct (concat-of-meta-fn term limit)
              :in-theory (e/d () ())))))

  (local
   (defthm valid-sc-concat-of-meta-fn-lemma1
     (implies (and (rp::valid-sc term a)
                   (or (IS-CONCAT-OF-CONCAT$ TERM)
                       (IS-CONCAT$-OF-CONCAT$ TERM)))
              (RP::VALID-SC (CADDDR (CADDR TERM)) A))
     :hints (("Goal"
              :in-theory (e/d (IS-CONCAT-OF-CONCAT$
                               rp::is-rp
                               rp::is-if
                               IS-CONCAT$-OF-CONCAT$) ())))))
  (local
   (defthm valid-sc-concat-of-meta-fn
     (implies (rp::valid-sc term a)
              (rp::valid-sc (mv-nth 0 (concat-of-meta-fn term limit)) a))
     :hints (("goal"
              :do-not-induct t
              :induct (concat-of-meta-fn term limit)
              :in-theory (e/d (rp::is-if rp::is-rp)
                              (rp::include-fnc
                               (:definition not)
                               (:definition natp)))))))
  

  (local
   (defthm rp-valid-termp-concat-of-meta-fn
     (implies (rp::rp-valid-termp term)
              (rp::rp-valid-termp (mv-nth 0 (concat-of-meta-fn term limit))))))

  (defthm  valid-rp-meta-rulep-concat-of-meta-fn-main
    (implies (and
              (concat-of-formula-checks state)
              (rp::rp-evl-meta-extract-global-facts :state state))
             (and
              (let ((rule (make rp::rp-meta-rule-rec
                                :fnc 'concat-of-meta-fn-main
                                :trig-fnc '4vec-concat
                                :dont-rw t
                                :valid-syntax t)))
                (and (rp::rp-meta-valid-syntaxp-sk rule state)
                     (rp::valid-rp-meta-rulep rule state)))))
    :otf-flg t
    :hints (("Goal"
             :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                             (rp::PSEUDO-TERMP2
                              natp
                              rp::PSEUDO-TERM-LISTP2
                              concat-of-meta-fn
;(:type-prescription acl2::logicp)
                              natp
;w
                              rp::RP-SYNTAXP
                              rp::VALID-SC)))))

  (defthm  valid-rp-meta-rulep-concat$-of-meta-fn-main
    (implies (and
              (concat-of-formula-checks state)
              (rp::rp-evl-meta-extract-global-facts :state state))
             (and
              (let ((rule (make rp::rp-meta-rule-rec
                                :fnc 'concat-of-meta-fn-main
                                :trig-fnc '4vec-concat$
                                :dont-rw t
                                :valid-syntax t)))
                (and (rp::rp-meta-valid-syntaxp-sk rule state)
                     (rp::valid-rp-meta-rulep rule state)))))
    :otf-flg t
    :hints (("Goal"
             :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                             (rp::PSEUDO-TERMP2
                              rp::PSEUDO-TERM-LISTP2
                              concat-of-meta-fn
                              natp
                              rp::RP-SYNTAXP
                              rp::VALID-SC))))))

;(bits-of-meta-fn '(bits '3 '4 (sbits '4 '5 n o)))

(encapsulate
  nil

  (local
   (defthm rp-evl-of-ex-from-rp
     (equal (rp::rp-evl (rp::ex-from-rp x) a)
            (rp::rp-evl x a))
     :hints (("goal"
              :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

  (local
   (defthmd rp-evl-of-ex-from-rp-reverse
     (implies (syntaxp (or (atom x)
                           (not (equal (car x)
                                       'rp::ex-from-rp))))
              (equal (rp::rp-evl x a)
                     (rp::rp-evl (rp::ex-from-rp x) a)))
     :hints (("goal"
              :in-theory '(rp-evl-of-ex-from-rp)))))

  (local
   (defthm valid-sc-bits-instance
     (equal (rp::valid-sc (list 'bits term (list 'quote x) (list 'quote y) ) a)
            (rp::valid-sc term a))
     :hints (("goal"
              :expand ((rp::valid-sc (list 'bits term (list 'quote x) (list 'quote y)) a))
              :in-theory (e/d (rp::is-rp rp::is-if) ())))))

  (local
   (in-theory (disable rp::ex-from-rp)))

  (local
   (defthm eval-when-is-bits-0-1-of-a-bitp
     (implies (and (is-bits-0-1-of-a-bitp term)
                   (rp-evl-meta-extract-global-facts)
                   (bits-of-formula-checks state)
                   (rp::valid-sc term a))
              (bitp (rp::rp-evl (caddr (cadr term)) a)))
     :hints (("goal"
              :do-not '(preprocess)
              :expand ((rp::valid-sc (cadr term) a)
                       (RP::EX-FROM-RP (CADR TERM))
                       (RP::CONTEXT-FROM-RP (CADR TERM) NIL)
                       (RP::VALID-SC (RP::EX-FROM-RP (CADR TERM))
                                     A)
                       (RP::VALID-SC (RP::EX-FROM-RP (CADDR (CADR TERM)))
                                     A)
                       (RP::EX-FROM-RP (LIST 'BITP
                                             (RP::EX-FROM-RP (CADDR (CADR TERM)))))
                       (rp::valid-sc-subterms (cdddr term) a)
                       (rp::valid-sc-subterms (cddr term) a)
                       (rp::valid-sc-subterms (cdr term) a)
                       (rp::valid-sc term a)
                       (rp::context-from-rp (cadddr term) nil))
              :in-theory (e/d (is-bits-0-1-of-a-bitp
                               rp-evl-of-ex-from-rp
                               rp::is-if rp::is-rp)
                              (bitp
                               ))))))

  (local
   (defthm valid-sc-implies-when-is-bits-of-sbits
     (implies (and (rp::valid-sc term a)
                   (rp-evl-meta-extract-global-facts)
                   (bits-of-formula-checks state)
                   (is-bits-of-sbits term))
              (and (rp::valid-sc (cadddr (rp::ex-from-rp (cadr term)))
                                 a)
                   (rp::valid-sc (car (cddddr (rp::ex-from-rp (cadr term))))
                                 a)))
     :hints (("goal"
              :expand ((rp::valid-sc-subterms (cdr term) a)
                       (rp::valid-sc term a)
                       (rp::valid-sc-subterms (cdddr term) a)
                       (rp::valid-sc-subterms (cddr term) a)
                       (rp::valid-sc (cadddr term) a)
                       (RP::VALID-SC (CADR TERM) A))
              :in-theory (e/d (rp::is-rp
                               is-bits-of-sbits
                               rp::ex-from-rp
                               rp::is-if) ())))))

  (local
   (defthmd rp-evl-of-sbits-when-is-bits-of-sbits-lemma
     (implies (and (syntaxp (equal term 'term))
                   (rp-evl-meta-extract-global-facts)
                   (bits-of-formula-checks state))
              (equal (rp::rp-evl (cadr term) a)
                     (rp::rp-evl (rp::ex-from-rp (cadr term)) a)))))

  (local
   (defthm rp-evl-of-sbits-when-is-bits-of-sbits
     (implies (and (is-bits-of-sbits term)
                   (rp-evl-meta-extract-global-facts)
                   (bits-of-formula-checks state))
              (EQUAL (rp::rp-evl (cadr term) a)
                     (sbits (cadr (cadr (rp::ex-from-rp (cadr term))))
                            (cadr (caddr (rp::ex-from-rp (cadr term))))
                            (rp::rp-evl (cadddr (rp::ex-from-rp (cadr term)))
                                        a)
                            (rp::rp-evl (car (cddddr (rp::ex-from-rp (cadr term))))
                                        a))))
     :hints (("goal"
              :in-theory (e/d (is-bits-of-sbits
                               rp-evl-of-fncall-args
                               rp-evl-of-sbits-when-is-bits-of-sbits-lemma
                               rp::ex-from-rp
                               rp::is-rp)
                              (rp-evl-of-ex-from-rp))))))

  (local
   (defthm valid-sc-implies-when-is-IS-BITS-OF-BITAND/OR/XOR
     (implies (and (rp::valid-sc term a)
                   (rp-evl-meta-extract-global-facts)
                   (bits-of-formula-checks state)
                   (IS-BITS-OF-BITAND/OR/XOR term))
              (and (RP::VALID-SC (CADR (CADR TERM)) A)
                   (RP::VALID-SC (CADDR (CADR TERM)) A)))
     :hints (("goal"
              :expand ((rp::valid-sc-subterms (cdr term) a)
                       (rp::valid-sc term a)
                       (rp::valid-sc-subterms (cdddr term) a)
                       (rp::valid-sc-subterms (cddr term) a)
                       (rp::valid-sc (cadddr term) a)
                       (RP::VALID-SC (CADR TERM) A))
              :in-theory (e/d (rp::is-rp
                               IS-BITS-OF-BITAND/OR/XOR
                               rp::ex-from-rp
                               rp::is-if) ())))))

  (local
   (defthm rp-evl-of-when-IS-BITS-OF-BITAND/OR/XOR
     (implies (and (rp-evl-meta-extract-global-facts)
                   (IS-BITS-OF-BITAND/OR/XOR term)
                   (bits-of-formula-checks state)
                   (equal (rp-evl x a) (BITS (RP-EVL (CADR (CADR TERM)) A)
                                             (RP-EVL (CADDR TERM) A)
                                             (RP-EVL (CADDDR TERM) A)))
                   (equal (rp-evl y a) (BITS (RP-EVL (CADDR (CADR TERM)) A)
                                             (RP-EVL (CADDR TERM) A)
                                             (RP-EVL (CADDDR TERM) A))))
              (EQUAL (RP-EVL (LIST (CAR (CADR TERM)) x y) A)
                     (BITS (RP-EVL (CADR TERM) A)
                           (RP-EVL (CADDR TERM) A)
                           (RP-EVL (CADDDR TERM) A))))
     :hints (("Goal"
              :in-theory (e/d (IS-BITS-OF-BITAND/OR/XOR) ())))))

  (defthm eval-of-bits-of-meta-fn
    (implies (and (rp::valid-sc term a)
                  (rp-evl-meta-extract-global-facts)
                  (bits-of-formula-checks state))
             (EQUAL (rp::rp-evl (mv-nth 0 (bits-of-meta-fn term)) a)
                    (rp::rp-evl term a)))
    :hints (("goal"
             :do-not-induct t
             :induct (bits-of-meta-fn term)
             :in-theory (e/d (rp::is-rp
                              rp-evl-of-fncall-args
                              rp::is-if)
                             ((:definition not)
                              (:definition natp))))))


  (local
   (defthmd rp-syntaxp-when-is-bits-of-sbits-lemma1
     (implies (syntaxp (equal term 'term))
              (equal (rp::rp-syntaxp term)
                     (rp::rp-syntaxp (rp::ex-from-rp term))))
     :rule-classes :rewrite
     :hints (("Goal"
              :in-theory (e/d (rp::ex-from-rp
                               rp::is-rp) ())))))

  (local
   (defthmd rp-syntaxp-when-is-bits-of-sbits-lemma2
     (implies (syntaxp (equal term 'term))
              (equal (rp::rp-syntaxp (cadr term))
                     (rp::rp-syntaxp (rp::ex-from-rp (cadr term)))))
     :rule-classes :rewrite
     :hints (("Goal"
              :use ((:instance rp-syntaxp-when-is-bits-of-sbits-lemma1
                               (term (cadr term))))
              :in-theory (e/d (rp::ex-from-rp
                               natp
                               rp::is-rp) ())))))

  (local
   (defthm rp-syntaxp-when-is-bits-of-sbits
     (implies (and (is-bits-of-sbits term)
                   (rp::rp-syntaxp term))
              (and (rp::rp-syntaxp (cadddr (rp::ex-from-rp (cadr term))))
                   (rp::rp-syntaxp (car (cddddr (rp::ex-from-rp (cadr
                                                                 term)))))))
     :hints (("goal"
              :do-not '(preprocess)
              :expand ((RP::RP-SYNTAXP-LST (CDDDR (RP::EX-FROM-RP (CADR
                                                                   TERM))))
                       (RP::RP-SYNTAXP-LST (CDDR (RP::EX-FROM-RP (CADR
                                                                  TERM))))
                       (RP::RP-SYNTAXP-LST (CDR (RP::EX-FROM-RP (CADR TERM))))
                       (RP::RP-SYNTAXP (RP::EX-FROM-RP (CADR TERM))))
              :in-theory (e/d (is-bits-of-sbits
                               rp-syntaxp-when-is-bits-of-sbits-lemma2) ())))))

  (local
   (defthm rp-syntaxp-bits-of-meta-fn
     (implies (rp::rp-syntaxp term)
              (rp::rp-syntaxp (mv-nth 0 (bits-of-meta-fn term))))
     :hints (("Goal"
              :induct (bits-of-meta-fn term)
              :do-not-induct t
              :in-theory (e/d ()
                              ((:DEFINITION NOT)
                               (:REWRITE ASSOCIATIVITY-OF-+)
                               (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
                               (:REWRITE COMMUTATIVITY-OF-+)
                               (:DEFINITION NATP)))))))

  (local
   (defthm pseudo-termp2-bits-of-meta-fn-lemma1
     (implies (and (IS-BITS-OF-CONCAT TERM)
                   (rp::pseudo-termp2 term))
              (RP::PSEUDO-TERMP2 (CADDDR (CADR TERM))))
     :hints (("Goal"
              :in-theory (e/d (IS-BITS-OF-CONCAT) ())))))

  (local
   (defthmd pseudo-termp2-bits-of-meta-fn-when-IS-BITS-OF-SBITS-lemma1
     (implies (rp::pseudo-termp2 term)
              (rp::pseudo-termp2 (rp::ex-from-rp term)))
     :hints (("Goal"
              :in-theory (e/d (rp::ex-from-rp
                               rp::is-rp) ())))))

  (local
   (defthm pseudo-termp2-bits-of-meta-fn-when-IS-BITS-OF-SBITS
     (implies (and (IS-BITS-OF-SBITS TERM)
                   (rp::pseudo-termp2 term))
              (and (RP::PSEUDO-TERMP2 (CAR (CDDDDR (RP::EX-FROM-RP (CADR
                                                                    TERM)))))
                   (RP::PSEUDO-TERMP2 (CADDDR (RP::EX-FROM-RP (CADR TERM))))))
     :hints (("Goal"
              :use ((:instance
                     pseudo-termp2-bits-of-meta-fn-when-IS-BITS-OF-SBITS-lemma1
                     (term (cadr term))))
; :expand ((rp::pseudo-termp2 (rp::ex-from-rp (cadddr term))))
              :in-theory (e/d (IS-BITS-OF-SBITS
                               rp::ex-from-rp) ())))))

  (local
   (defthm pseudo-termp2-bits-of-meta-fn
     (implies (rp::pseudo-termp2 term)
              (rp::pseudo-termp2 (mv-nth 0 (bits-of-meta-fn term))))
     :hints (("Goal"
              :induct (bits-of-meta-fn term)
              :do-not-induct t
              :in-theory (e/d ()
                              ((:DEFINITION NOT)
                               (:REWRITE ASSOCIATIVITY-OF-+)
                               (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
                               (:REWRITE COMMUTATIVITY-OF-+)
                               (:DEFINITION NATP)
                               (:DEFINITION MIN)
                               (:REWRITE BITP-IMPLIES-NATP)
                               (:DEFINITION BITP)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION MEMBER-EQUAL)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                               (:REWRITE DEFAULT-CAR)
                               (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-3)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-2)
                               (:DEFINITION ACL2::WEAK-APPLY$-BADGE-P)
                               (:TYPE-PRESCRIPTION LEN)
                               (:DEFINITION LEN)
                               (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                               (:DEFINITION TRUE-LISTP)
                               (:REWRITE DEFAULT-+-2)
                               (:REWRITE DEFAULT-+-1)))))))

  (local
   (defthmd all-falist-consistent-bits-of-meta-fn-when-IS-BITS-OF-SBITS-lemma
     (implies (rp::all-falist-consistent term)
              (rp::all-falist-consistent (rp::ex-from-rp term)))
     :hints (("Goal"
              :in-theory (e/d (rp::ex-from-rp
                               rp::is-rp) ())))))

  (local
   (defthm all-falist-consistent-bits-of-meta-fn-when-IS-BITS-OF-SBITS
     (implies (and (IS-BITS-OF-SBITS TERM)
                   (rp::all-falist-consistent term))
              (and (RP::ALL-FALIST-CONSISTENT (CAR (CDDDDR (RP::EX-FROM-RP
                                                            (CADR TERM)))))
                   (RP::ALL-FALIST-CONSISTENT (CADDDR (RP::EX-FROM-RP (CADR
                                                                       TERM))))))
     :hints (("Goal"
              :use ((:instance
                     all-falist-consistent-bits-of-meta-fn-when-IS-BITS-OF-SBITS-lemma
                     (term (cadr term))))
              :in-theory (e/d (IS-BITS-OF-SBITS) ())))))

  (local
   (defthm all-falist-consistent-bits-of-meta-fn
     (implies (rp::all-falist-consistent term)
              (rp::all-falist-consistent (mv-nth 0 (bits-of-meta-fn term))))
     :hints (("Goal"
              :induct (bits-of-meta-fn term)
              :do-not-induct t
              :in-theory (e/d ()
                              ((:DEFINITION NOT)
                               (:REWRITE ASSOCIATIVITY-OF-+)
                               (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
                               (:REWRITE COMMUTATIVITY-OF-+)
                               (:DEFINITION NATP)
                               (:DEFINITION TRUE-LISTP)))))))

  (defthm rp-valid-termp-bits-of-meta-fn
    (implies (rp::rp-valid-termp term)
             (rp::rp-valid-termp (mv-nth 0 (bits-of-meta-fn term))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d ()
                             (rp::all-falist-consistent
                              bits-of-meta-fn
                              rp::pseudo-termp2
                              rp::rp-syntaxp)))))

  (defthm valid-sc-resolve-bits-of-meta-fn
    (implies (and (rp::valid-sc term a)
                  (rp-evl-meta-extract-global-facts)
                  (bits-of-formula-checks state))
             (rp::valid-sc (mv-nth 0 (bits-of-meta-fn term)) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (bits-of-meta-fn term)
             :in-theory (e/d (rp::is-if rp::is-rp
                                        IS-BITS-OF-BITAND/OR/XOR)
                             (rp::INCLUDE-FNC
                              (:DEFINITION NOT)
                              (:REWRITE BITP-IMPLIES-NATP)
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                              (:DEFINITION BITP)
                              (:DEFINITION ACL2::APPLY$-BADGEP)
                              (:DEFINITION SUBSETP-EQUAL)
                              (:DEFINITION MEMBER-EQUAL)
                              (:REWRITE DEFAULT-CDR)
                              (:REWRITE
                               ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                              (:REWRITE DEFAULT-CAR)
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:DEFINITION RP::EVAL-AND-ALL)
                              (:REWRITE
                               ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-3)
                              (:DEFINITION natp))))))

  (defthm valid-rp-meta-rulep-bits-of-meta-fn
    (implies (and (rp-evl-meta-extract-global-facts)
                  (bits-of-formula-checks state))
             (let ((rule (make rp::rp-meta-rule-rec
                               :fnc 'bits-of-meta-fn
                               :trig-fnc 'bits
                               :dont-rw t
                               :valid-syntax t)))
               (and (rp::rp-meta-valid-syntaxp-sk rule state)
                    (rp::valid-rp-meta-rulep rule state))))
    :otf-flg t
    :hints (("Goal"
             :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                             (rp::PSEUDO-TERMP2
                              rp::PSEUDO-TERM-LISTP2
                              bits-of-meta-fn
                              rp::RP-SYNTAXP
                              rp::VALID-SC))))))

(in-theory
 (disable bits-of-sbits-4
          bits-of-sbits-5
          bits-of-sbits-3
          bits-of-sbits-2
          bits-of-sbits-1))

(rp::add-meta-rules bits-of-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc 'bits-of-meta-fn
                                :trig-fnc 'bits
                                :dont-rw t
                                :valid-syntax t)))

(rp::add-meta-rules concat-of-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc 'concat-of-meta-fn-main
                                :trig-fnc '4vec-concat
                                :dont-rw t
                                :valid-syntax t)
                          (make rp::rp-meta-rule-rec
                                :fnc 'concat-of-meta-fn-main
                                :trig-fnc '4vec-concat$
                                :dont-rw t
                                :valid-syntax t))
                    4vec-concat-of)

(in-theory (disable sv::4vec-p-when-maybe-4vec-p))

(verify-guards concat-of-meta-fn-main)
