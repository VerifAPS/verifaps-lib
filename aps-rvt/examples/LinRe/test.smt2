
;;m   := (y2 - y1) * ICONST / (x2 - x1);


;; m := (y2 - y1) * ICONST / (x2 - x1)
;; -1*    [ (y2 - y1) * ICONST / (x2 - x1) ]
;;  [ -1 * (y2 - y1) * ICONST / (x2 - x1) ]

;; (-y2 + y1) * ICONST / (x2 - x1)


(define-fun m ((x1 Int) (x2 Int) (y1 Int) (y2 Int)) Int
  (let ((ydiff (- y2 y1)) (xdiff (- x2 x1)))
    (div (* 1000 ydiff) xdiff)))

;;t   := y1 - m * x1 / ICONST;
(define-fun t ((m Int) (x1 Int) (y1 Int)) Int
  (- y1 (div (* m x1) 1000)))

(define-fun out ((m Int) (t Int) (i Int)) Int
  (+ (div (* m i) 1000) t))


(assert
 (forall ((y1 Int) (y2 Int) (x1 Int) (x2 Int))
         (let ((m1 (m x1 x2 y1 y2))
               (m2 (m x2 x1 (- y2) (- y1))))
           (let ((t1 (t m1 x1 (- y1)))
                 (t2 (t m2 x1 (- y1))))
                                        ;         (forall ((in Int))
             (= m1 (- m2))))))

                                        ;(out m1 t1 in) (out (- m2) t2 in)))))))

(check-sat)
(get-model)
;;(get-value ((m x1 x2 y1 y2)
;;            (m x2 x1 (- y2) (- y1))))
