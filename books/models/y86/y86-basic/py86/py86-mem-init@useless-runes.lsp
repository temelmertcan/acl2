(RMBYTES
 (156 78 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 (2 1 (:TYPE-PRESCRIPTION NATP-RM08))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(M86-CLEAR-MEM-DWORD-ADDR
 (200 100 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(M86-CLEAR-MEM-DWORD-ADDR-PRESERVES-X86-32P
 (12 12 (:LINEAR INDEX-OF-<-LEN))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ASH-ADDR--2-IS-LESS-WITH-EXPLODED-N32P
 (1 1 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(M86-CLEAR-MEM
 (112 56 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (29 29 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(M86-REGP)
(M86-REG-UPDATES
 (974 327 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (720 360 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (640 640 (:TYPE-PRESCRIPTION BOOLEANP))
 (58 58 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (52 26 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (46 46 (:LINEAR INDEX-OF-<-LEN))
 (30 29 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(M86-REG-UPDATES-PRESERVES-X86-32P
 (2338 781 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1552 1552 (:TYPE-PRESCRIPTION BOOLEANP))
 (156 156 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (90 45 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (54 54 (:REWRITE DEFAULT-<-2))
 (54 54 (:REWRITE DEFAULT-<-1))
 (30 30 (:LINEAR INDEX-OF-<-LEN))
 (5 5 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(M86-MEMP)
(M86-MEM-UPDATES
 (328 164 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (36 34 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (24 12 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (18 18 (:LINEAR INDEX-OF-<-LEN))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(M86-MEM-UPDATES-PRESERVES-X86-32P
 (38 38 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (18 18 (:LINEAR INDEX-OF-<-LEN))
 (16 8 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 )
(M32-GET-REGS-AND-FLAGS
 (40 20 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (16 8 (:TYPE-PRESCRIPTION NATP-RGFI))
 (2 1 (:TYPE-PRESCRIPTION NATP-EIP))
 )
(M86-CLEAR-REGS
 (40 20 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 )
(M86-CLEAR-REGS-PRESERVES-X86-32P
 (20 10 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 )
(INIT-Y86-STATE
 (208 78 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (136 68 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (128 128 (:TYPE-PRESCRIPTION BOOLEANP))
 (74 74 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (48 8 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (32 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-<-2))
 (24 8 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (15 1 (:DEFINITION M86-MEMP))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (12 6 (:REWRITE GL::NFIX-NATP))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(INIT-Y86-STATE-PRESERVES-X86-32P
 (20 10 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 )
