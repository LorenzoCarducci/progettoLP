;;;; <Matricola> <Cognome> <Nome>
;;;; Type checker minimale per Lisp (interi + bool + simboli + liste + built-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; STATO GLOBALE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *tc-errors* nil)
(defvar *next-tvar-id* 0)

(defun tc-reset ()
  (setf *tc-errors* nil
        *next-tvar-id* 0))

(defun tc-add-error (msg)
  (push msg *tc-errors*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LETTURA FILE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun read-all-forms-from-file (pathname)
  (with-open-file (in pathname :direction :input)
    (let ((*read-eval* nil)
          (forms '()))
      (loop
        for form = (read in nil :eof)
        until (eq form :eof)
        do (push form forms))
      (nreverse forms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; RAPPRESENTAZIONE TIPI
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tipo:
;;   :int | :bool | :symbol | :string | :char | :unknown
;;   (:list T)
;;   (:fun (req...) (opt...) ret)
;;   (:var id)

(defun make-tvar ()
  (incf *next-tvar-id*)
  `(:var ,*next-tvar-id*))

(defun tvar-p (ty)
  (and (consp ty) (eq (first ty) :var)))

(defun list-type-p (ty)
  (and (consp ty) (eq (first ty) :list)))

(defun fun-type-p (ty)
  (and (consp ty) (eq (first ty) :fun)))

(defun fun-req (ft) (second ft))
(defun fun-opt (ft) (third ft))
(defun fun-ret (ft) (fourth ft))

(defun make-list-type (elem)
  `(:list ,elem))

(defun make-fun-type (req opt ret)
  `(:fun ,(copy-list req) ,(copy-list opt) ,ret))

(defun literal-type (v)
  (cond
    ((integerp v) :int)
    ((or (eq v t) (eq v nil)) :bool)
    ((stringp v) :string)
    ((characterp v) :char)
    ((symbolp v) :symbol)
    (t :unknown)))

(defun quote-type (obj)
  (cond
    ((integerp obj) :int)
    ((symbolp obj)  :symbol)
    ((consp obj)
     (if (null obj)
         (make-list-type :unknown)
         (let ((elem-type (quote-type (first obj))))
           (dolist (el (rest obj))
             (let ((t2 (quote-type el)))
               (unless (equal t2 elem-type)
                 (setf elem-type :unknown))))
           (make-list-type elem-type))))
    (t :unknown)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SOSTITUZIONI & UNIFICAZIONE (usa hash-table solo internamente)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun empty-subst ()
  (make-hash-table :test #'eql))

(defun subst-lookup (subst var)
  (gethash (second var) subst))

(defun subst-extend (subst var ty)
  (setf (gethash (second var) subst) ty)
  subst)

(defun subst-apply (subst ty)
  (labels ((rec (x)
             (cond
               ((tvar-p x)
                (let ((b (subst-lookup subst x)))
                  (if b (rec b) x)))
               ((list-type-p x)
                (make-list-type (rec (second x))))
               ((fun-type-p x)
                (make-fun-type (mapcar #'rec (fun-req x))
                               (mapcar #'rec (fun-opt x))
                               (rec (fun-ret x))))
               (t x))))
    (rec ty)))

(defun occurs-in? (var ty subst)
  (let ((ty* (subst-apply subst ty)))
    (cond
      ((equal ty* var) t)
      ((list-type-p ty*)
       (occurs-in? var (second ty*) subst))
      ((fun-type-p ty*)
       (or (some (lambda (p) (occurs-in? var p subst)) (fun-req ty*))
           (some (lambda (p) (occurs-in? var p subst)) (fun-opt ty*))
           (occurs-in? var (fun-ret ty*) subst)))
      (t nil))))

(defun unify (ty1 ty2 subst)
  "Unifica ty1 e ty2 aggiornando subst.
   Ritorna :fail in caso di conflitto di tipo."
  (let* ((a (subst-apply subst ty1))
         (b (subst-apply subst ty2)))
    (cond
      ((equal a b) subst)

      ((tvar-p a)
       (if (occurs-in? a b subst)
           :fail
           (subst-extend subst a b)))

      ((tvar-p b)
       (if (occurs-in? b a subst)
           :fail
           (subst-extend subst b a)))

      ;; :unknown come jolly (permette qualcosa di tipo molto lasco)
      ((eq a :unknown) (unify (make-tvar) b subst))
      ((eq b :unknown) (unify a (make-tvar) subst))

      ((and (list-type-p a) (list-type-p b))
       (unify (second a) (second b) subst))

      ((and (fun-type-p a) (fun-type-p b))
       (let ((ra (fun-req a))
             (rb (fun-req b))
             (oa (fun-opt a))
             (ob (fun-opt b))
             (s subst))
         (when (or (/= (length ra) (length rb))
                   (/= (length oa) (length ob)))
           (return-from unify :fail))
         (loop for pa in ra for pb in rb
               do (setf s (unify pa pb s))
               when (eq s :fail) do (return-from unify :fail))
         (loop for pa in oa for pb in ob
               do (setf s (unify pa pb s))
               when (eq s :fail) do (return-from unify :fail))
         (setf s (unify (fun-ret a) (fun-ret b) s))
         (if (eq s :fail) :fail s)))

      (t
       (if (equal a b) subst :fail)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; AMBIENTE & BUILT-IN (tutto in una semplice alist, niente hash-table)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ambiente = alist (sym . type)

(defun env-lookup (env sym)
  (let ((pair (assoc sym env)))
    (if pair (cdr pair) :unknown)))

(defun env-extend (env sym ty)
  (acons sym ty env))

(defun tc-init-builtins ()
  "Ambiente iniziale con tipi dei built-in."
  (list
   ;; aritmetica interi
   (cons '+  (make-fun-type (list :int :int) '() :int))
   (cons '-  (make-fun-type (list :int :int) '() :int))
   (cons '*  (make-fun-type (list :int :int) '() :int))
   (cons '/  (make-fun-type (list :int :int) '() :int))
   (cons '1+ (make-fun-type (list :int) '() :int))
   (cons '1- (make-fun-type (list :int) '() :int))
   (cons 'zerop (make-fun-type (list :int) '() :bool))
   ;; logica
   (cons 'not  (make-fun-type (list :bool) '() :bool))
   (cons 'and  (make-fun-type (list :bool :bool) '() :bool))
   (cons 'or   (make-fun-type (list :bool :bool) '() :bool))
   ;; confronti interi
   (cons '=  (make-fun-type (list :int :int) '() :bool))
   (cons '<  (make-fun-type (list :int :int) '() :bool))
   (cons '<= (make-fun-type (list :int :int) '() :bool))
   (cons '>  (make-fun-type (list :int :int) '() :bool))
   (cons '>= (make-fun-type (list :int :int) '() :bool))
   ;; liste
   (cons 'cons  (make-fun-type
                 (list (make-tvar)
                       (make-list-type (make-tvar)))
                 '()
                 (make-list-type (make-tvar))))
   (cons 'car   (make-fun-type
                 (list (make-list-type (make-tvar)))
                 '()
                 (make-tvar)))
   (cons 'cdr   (make-fun-type
                 (list (make-list-type (make-tvar)))
                 '()
                 (make-list-type (make-tvar))))
   (cons 'list  (make-fun-type
                 '()
                 (list (make-tvar))
                 (make-list-type (make-tvar))))
   (cons 'length (make-fun-type
                  (list (make-list-type (make-tvar)))
                  '()
                  :int))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PRETTY PRINT TIPI (per la riga FTYPE)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun human-type (ty)
  (let ((t2 (subst-apply (empty-subst) ty)))
    (cond
      ((eq t2 :int) "integer")
      ((eq t2 :bool) "boolean")
      ((eq t2 :symbol) "symbol")
      ((eq t2 :string) "string")
      ((eq t2 :char) "character")
      ((list-type-p t2)
       (format nil "list(~A)" (human-type (second t2))))
      ((fun-type-p t2)
       (let ((args (mapcar #'human-type (fun-req t2)))
             (opts (mapcar #'human-type (fun-opt t2)))
             (ret  (human-type (fun-ret t2))))
         (with-output-to-string (out)
           (princ "function (" out)
           (loop
             for a in args
             for idx from 0
             do (when (> idx 0) (princ " " out))
                (princ a out))
           (when opts
             (when args (princ " " out))
             (princ "&optional" out)
             (dolist (o opts)
               (princ " " out)
               (princ o out)))
           (princ ") " out)
           (princ ret out)))
      ((tvar-p t2)
       (format nil "T~A" (second t2)))
      (t "unknown")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; INFERENZA ESPRESSIONI
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun infer-expr (expr env subst)
  "Restituisce (values tipo nuovo-subst)."
  (cond
    ;; literal
    ((or (integerp expr)
         (stringp expr)
         (characterp expr)
         (eq expr t)
         (eq expr nil))
     (values (literal-type expr) subst))

    ;; variabile
    ((symbolp expr)
     (values (env-lookup env expr) subst))

    ;; quote
    ((and (consp expr) (eq (first expr) 'quote))
     (values (quote-type (second expr)) subst))

    ;; if
    ((and (consp expr) (eq (first expr) 'if))
     (destructuring-bind (if-key test-expr then-expr else-expr) expr
       (declare (ignore if-key))
       (multiple-value-bind (tt subst1) (infer-expr test-expr env subst)
         (let ((s2 (unify tt :bool subst1)))
           (when (eq s2 :fail)
             (tc-add-error (format nil
                                   "Condition ~S is not boolean (type ~A)."
                                   test-expr (human-type tt)))
             (setf s2 subst1))
           (multiple-value-bind (t-then subst2)
               (infer-expr then-expr env s2)
             (multiple-value-bind (t-else subst3)
                 (infer-expr else-expr env subst2)
               (let ((s4 (unify t-then t-else subst3)))
                 (if (eq s4 :fail)
                     (values :unknown subst3)
                     (values (subst-apply s4 t-then) s4))))))))

    ;; let
    ((and (consp expr) (eq (first expr) 'let))
     (destructuring-bind (let-key bindings &rest body) expr
       (declare (ignore let-key))
       (let ((env2 env)
             (subst2 subst))
         (dolist (binding bindings)
           (destructuring-bind (var val-expr) binding
             (multiple-value-bind (tyv subst3)
                 (infer-expr val-expr env2 subst2)
               (setf env2 (env-extend env2 var tyv)
                     subst2 subst3))))
         (infer-progn body env2 subst2))))

    ;; progn
    ((and (consp expr) (eq (first expr) 'progn))
     (infer-progn (rest expr) env subst))

    ;; format → controlliamo solo gli argomenti
    ((and (consp expr) (eq (first expr) 'format))
     (let ((s subst))
       (dolist (a (rest expr))
         (multiple-value-bind (ta s2) (infer-expr a env s)
           (declare (ignore ta))
           (setf s s2)))
       (values :unknown s)))

    ;; chiamata di funzione generica
    ((consp expr)
     (let ((fn (first expr))
           (args (rest expr)))
       (let* ((proto (env-lookup env fn)))
         (if (not (fun-type-p proto))
             ;; funzione sconosciuta: nessun controllo
             (values :unknown subst)
             (let ((arg-types '())
                   (s subst))
               ;; inferisci tipi argomenti
               (dolist (a args)
                 (multiple-value-bind (ta s2) (infer-expr a env s)
                   (push ta arg-types)
                   (setf s s2)))
               (setf arg-types (nreverse arg-types))
               (let ((req (fun-req proto))
                     (opt (fun-opt proto))
                     (argc (length arg-types))
                     (minc (length req))
                     (maxc (+ (length req) (length opt))))
                 (when (or (< argc minc) (> argc maxc))
                   (tc-add-error
                    (format nil
                            "Wrong number of arguments in call ~S (expected ~D..~D, got ~D)."
                            expr minc maxc argc)))
                 (let ((s2 s))
                   (loop for at in arg-types
                         for pt in (append req opt)
                         for i from 1
                         do (when pt
                              (let ((s3 (unify at pt s2)))
                                (when (eq s3 :fail)
                                  (tc-add-error
                                   (format nil
                                           "Type error in call ~S: argument ~D (~S) has type ~A, expected ~A."
                                           expr i (nth (1- i) args)
                                           (human-type at) (human-type pt)))
                                  (setf s3 s2))
                                (setf s2 s3))))
                   (values (fun-ret proto) s2)))))))

    (t
     (values :unknown subst))))))

(defun infer-progn (forms env subst)
  (let ((current-type :unknown)
        (s subst))
    (dolist (f forms)
      (multiple-value-bind (tf s2) (infer-expr f env s)
        (setf current-type tf
              s s2)))
    (values current-type s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DEFUN TOP-LEVEL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun process-defun (form env subst)
  "Analizza una DEFUN, inferisce il tipo e stampa la riga ftype."
  (destructuring-bind (defun-key name params &rest body) form
    (declare (ignore defun-key))
    (let ((req-types '())
          (opt-types '())
          (param-names '())
          (opt-mode nil))
      (dolist (p params)
        (cond
          ((eq p '&optional)
           (setf opt-mode t))
          (opt-mode
           (let ((v (if (symbolp p) p (first p))))
             (push v param-names)
             (push (make-tvar) opt-types)))
          (t
           (push p param-names)
           (push (make-tvar) req-types))))
      (setf req-types (nreverse req-types)
            opt-types (nreverse opt-types)
            param-names (nreverse param-names))
      (let* ((ret-type (make-tvar))
             (fun-type (make-fun-type req-types opt-types ret-type))
             (env2 (env-extend env name fun-type))
             (subst2 subst))
        ;; aggiungi parametri all'ambiente del corpo
        (dolist (pair (mapcar #'cons param-names
                              (append req-types opt-types)))
          (setf env2 (env-extend env2 (car pair) (cdr pair))))
        ;; inferisci il tipo del corpo
        (multiple-value-bind (body-type subst3)
            (infer-progn body env2 subst2)
          ;; unifica tipo di ritorno con quello del corpo
          (let ((s4 (unify ret-type body-type subst3)))
            (when (eq s4 :fail)
              (tc-add-error
               (format nil
                       "Return type mismatch in function ~A: body has type ~A."
                       name (human-type body-type)))
              (setf s4 subst3))
            (let ((final-type (subst-apply s4 fun-type)))
              ;; stampa riga ftype stile traccia
              (princ "(ftype (function (" t)
              ;; parametri required
              (let ((firstp t))
                (dolist (rt (fun-req final-type))
                  (unless firstp (princ " " t))
                  (princ (human-type rt) t)
                  (setf firstp nil)))
              ;; optional
              (when (fun-opt final-type)
                (when (fun-req final-type) (princ " " t))
                (princ "&optional" t)
                (dolist (ot (fun-opt final-type))
                  (princ " " t)
                  (princ (human-type ot) t)))
              (princ ") " t)
              (princ (human-type (fun-ret final-type)) t)
              (princ ") " t)
              (princ name t)
              (princ ")" t)
              (terpri)
              ;; aggiorna ambiente con tipo definitivo
              (values (env-extend env name final-type) s4))))))))

(defun process-top-level-form (form env subst)
  (cond
    ((and (consp form) (eq (first form) 'defun))
     (process-defun form env subst))
    (t
     (multiple-value-bind (ty s2) (infer-expr form env subst)
       (declare (ignore ty))
       (values env s2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FUNZIONE PRINCIPALE TC
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun tc (filename)
  "Entry point del type checker."
  (tc-reset)
  (format t ";;; Type checking \"~A\".~%~%" filename)
  (let* ((forms (read-all-forms-from-file filename))
         (env   (tc-init-builtins))
         (subst (empty-subst)))
    (dolist (f forms)
      (multiple-value-bind (env2 subst2)
          (process-top-level-form f env subst)
        (setf env env2
              subst subst2)))
    ;; stampa eventuali errori
    (dolist (msg (nreverse *tc-errors*))
      (format t "Error: ~A~%" msg))
    (null *tc-errors*)))
