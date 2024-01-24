(set-logic ALL)
(set-option :interactive-mode true)

(declare-const a1 (_ BitVec 64))
(declare-const a2 (_ BitVec 64))
(declare-const b1 (_ BitVec 64))
(declare-const b2 (_ BitVec 64))
(declare-const c1 (_ BitVec 64))
(declare-const c2 (_ BitVec 64))

(declare-const n (_ BitVec 64))
(declare-const k (_ BitVec 64))

(define-fun separate ((a1 (_ BitVec 64))
                      (a2 (_ BitVec 64))
                      (b1 (_ BitVec 64))
                      (b2 (_ BitVec 64)))
  Bool
  (not
   (or
    (bvule (bvsub b1 a1) (bvsub a2 a1))
    (bvule (bvsub b2 a1) (bvsub a2 a1))
    (bvule (bvsub a1 b1) (bvsub b2 b1))
    (bvule (bvsub a2 b1) (bvsub b2 b1)))))

(define-fun subset ((a1 (_ BitVec 64))
                    (a2 (_ BitVec 64))
                    (b1 (_ BitVec 64))
                    (b2 (_ BitVec 64)))
  Bool
  (or
   (= (bvsub b2 b1) (_ bv18446744073709551615 64))
   (and (bvule (bvsub a2 b1) (bvsub b2 b1))
        (bvule (bvsub a1 b1) (bvsub a2 b1)))))

(push 1)

;; Theorem: mem_separate_for_subset2

;; Preferred solver: Bitwuzla (~60s)
;; z3 (~120s)
(assert (not
         (=> (and (separate a1 a2 b1 b2)
                  (subset c1 c2 b1 b2))
             (separate a1 a2 c1 c2))))

;; (assert (not
;;          (=> (and (separate a1 a2 b1 b2)
;;                   (subset c1 c2 a1 a2))
;;              (separate c1 c2 b1 b2))))


(check-sat)
(get-model)
;; (get-assertions)

(pop 1)

(push 1)

;; Theorem: mem_subset_trans

;; Preferred solver: z3 (~10s)
;; Bitwuzla (~288s)

(assert (not
         (=> (and (subset a1 a2 b1 b2)
                  (subset b1 b2 c1 c2))
             (subset a1 a2 c1 c2))))

(check-sat)
(get-model)
(pop 1)
