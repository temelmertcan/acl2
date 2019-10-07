; RP-REWRITER

; Noe: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019 Regents of the University of Texas
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

(include-book "aux-functions")

#|(encapsulate
  nil

  (defthm dont-rw-syntaxp-aux-cons
    (equal (dont-rw-syntaxp-aux (cons a b))
           (AND (OR (atom a)
                   ; (strict-quotep a)
                    (DONT-RW-SYNTAXP-AUX a))
                (DONT-RW-SYNTAXP-AUX b))))

  (defthm dont-rw-syntaxp-cons
    (equal (dont-rw-syntaxp  (cons a b))
           (or nil;(strict-quotep (cons a b))
               (AND (OR (atom a)
                        ;(strict-quotep a)
                        (DONT-RW-SYNTAXP-AUX a))
                    (DONT-RW-SYNTAXP-AUX b))))
    :hints (("Goal"
             :in-theory (e/d (dont-rw-syntaxp) ())))))||#

(encapsulate
  nil
  (local
   (include-book "ihs/ihs-lemmas" :dir :system))

  (local
   (in-theory (disable acl2::logcdr
                       acl2::logcar
                       logapp)))

  (defthm natp-logcdr
    (implies (and (natp x))
             (natp (acl2::logcdr x)))
    :rule-classes :type-prescription)

  (defthm natp-logcar
    (implies (and (natp x))
             (natp (acl2::logcar x)))
    :rule-classes :type-prescription)

  (defthm natp-logapp
    (implies (and (natp y)
                  (natp x)
                  (natp size))
             (natp (logapp size x y)))
    :rule-classes :type-prescription)

  (defthm natp-ash
    (implies (and (natp y)
                  (integerp size))
             (natp (ash y size)))
    :hints (("Goal"
             :in-theory (e/d (ash) ())))
    :rule-classes :type-prescription)

  (defthm natp-logapp-rw
    (implies (and (natp y)
                  (natp x)
                  (natp size))
             (natp (logapp size x y)))))
