;;    *** Reasoning about an Instant-Runoff Voting Algorithm ***

;; Note: The license below is based on the template at:
;; http://opensource.org/licenses/BSD-3-Clause

;; Copyright (C) 2018, Shilpi Goel and Mayank Manjrekar
;; All rights reserved.

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holders nor the names of its
;;   contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Original Authors: Shilpi Goel      <shigoel@gmail.com>
;;                   Mayank Manjrekar <mankmonjre@gmail.com>

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defpkg "IRV"
  (union-eq
   '(
     binary-logand
     binary-logior
     binary-logxor
     lnfix

     a b c d e f g h i j k l m n o p q r s t u v w x y z lst

     definline
     def-gl-thm
     b*
     include-raw
     
     ;; XDOC
     defsection
     defxdoc
     top

     ;; TOOLS
     defprod
     def-ruleset
     def-ruleset!
     add-to-ruleset
     ruleset-theory
     enable*
     disable*
     e/d*

     IRV ; so that top-level :doc topic is also in "ACL2" package

     )
   (union-eq *acl2-exports*
             std::*std-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

;; ======================================================================
