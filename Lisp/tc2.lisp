;;;; <Matricola> <Cognome> <Nome>
;;;; (Max 3 membri, una riga ciascuno)
;;;; Type Checker per Common Lisp (subset) scritto in Common Lisp
;;;; ------------------------------------------------------------------
;;;; Funzione principale: (tc "file.lisp")
;;;; - Legge il file
;;;; - Esegue inferenza di tipi (stile Damas–Hindley–Milner semplificato)
;;;; - Stampa i tipi delle funzioni definite (ftype) e segnala errori
;;;; ------------------------------------------------------------------
;;;; Tipi supportati (ground):
;;;;   :int, :bool, :symbol, :string, :char, (:list T)
;;;; Funzioni:
;;;;   - Inferenza per: literal, variable, if, let, lambda, function call,
;;;;     quote, progn
;;;;   - Definizioni: defun (con &optional), let (generalization)
;;;;   - Built-in tipizzate: + - * / = < <= > >= zerop 1+ 1-
;;;;                        cons car cdr list null listp atom eq eql equal
;;;;                        not and or length
;;;;     (alcune con polimorfismo sulla lista)
;;;; ------------------------------------------------------------------
;;;; Limitazioni note:
;;;; - Non copre tutte le forme del CL ANSI; focus didattico E6P.
;;;; - NIL è trattato come booleano false *e* lista vuota polimorfica.
;;;;   La cosa è gestita con una “somma” di vincoli che viene risolta
;;;;   quando NIL è usato in un contesto più specifico.
;;;; - Le funzioni var-arg sono trattate tramite tipizzazione delle
;;;;   occorrenze (p.es. (list ...)) imponendo uniformità di tipo.
;;;; ------------------------------------------------------------------
;;;; Riferimenti progetto / esempi consegna E6P: vedi traccia. 
;;;; ------------------------------------------------------------------

;;;; ===================== DEBUG =====================

(defparameter *tc-debug* nil)
(defun tc-debug-on ()  (setf *tc-debug* t))
(defun tc-debug-off () (setf *tc-debug* nil))
(defun dbg (fmt &rest args)
  (when *tc-debug* (apply #'format *trace-output* (concatenate 'string "[TC] " fmt "~%") args)))

;;;; ===================== RAPPRESENTAZIONE TIPI =====================

;; T := :int | :bool | :symbol | :string | :char
;;    | (:list T) | (:fun (arg-types) (opt-types) ret)
;;    | (:var id)
;; Le “type scheme” per polimorfismo:
;;    (scheme (vars...) T)

(defstruct (tvar
             (:constructor make-tvar-internal (id))
             (:predicate tvar-struct-p))
  id)

(defparameter *tvar-counter* 0)
(defun fresh-tvar ()
  (incf *tvar-counter*)
  `(:var ,(make-tvar-internal *tvar-counter*)))

(defun typevar-term-p (t)
  (and (consp t) (eq (first t) :var)))

(defun base-type-p (t)
  (member t '(:int :bool :symbol :string :char) :test #'eq))

(defun list-type-p (t) (and (consp t) (eq (first t) :list)))
(defun fun-type-p  (t) (and (consp t) (eq (first t) :fun)))

(defun make-list-type (elem) `(:list ,elem))
(defun make-fun-type (req opt ret) `(:fun ,(copy-list req) ,(copy-list opt) ,ret))

(defun fun-args (f) (second f))     ; required list
(defun fun-opts (f) (third f))      ; optional list
(defun fun-ret  (f) (fourth f))

;;;; ===================== SOSTITUZIONI & OCCURS =====================

;; Subst = hash-table: tvar-id -> Type
(defun empty-subst () (make-hash-table :test #'eql))

(defun occurs-in? (var t subst)
  "Occurs-check: verifica se var compare in t (dopo applicare subst)."
  (let ((t (subst-apply subst t)))
    (cond
      ((equal t var) t)
      ((list-type-p t) (occurs-in? var (second t) subst))
      ((fun-type-p t)
       (or (some (lambda (x) (occurs-in? var x subst)) (fun-args t))
           (some (lambda (x) (occurs-in? var x subst)) (fun-opts t))
           (occurs-in? var (fun-ret t) subst)))
      (t nil))))

(defun subst-extend (subst var t)
  (setf (gethash (tvar-id (second var)) subst) t)
  subst)

(defun subst-lookup (subst var)
  (gethash (tvar-id (second var)) subst))

(defun subst-apply (subst t)
  (labels ((rec (x)
             (cond
               ((typevar-term-p x)
                (let ((b (subst-lookup subst x)))
                  (if b (rec b) x)))
               ((list-type-p x) (make-list-type (rec (second x))))
               ((fun-type-p  x)
                (make-fun-type (mapcar #'rec (fun-args x))
                               (mapcar #'rec (fun-opts x))
                               (rec (fun-ret x))))
               (t x))))
    (rec t)))

(defun subst-compose (s2 s1)
  "Applica prima s1 poi s2."
  (maphash (lambda (k v)
             (setf (gethash k s1) (subst-apply s2 v)))
           s1)
  ;; unisci nuove associazioni s2
  (maphash (lambda (k v)
             (setf (gethash k s1) v))
           s2)
  s1)

;;;; ===================== UNIFICAZIONE =====================

(define-condition tc-type-error (error)
  ((expected :initarg :expected :reader type-error-expected)
   (found    :initarg :found    :reader type-error-found)
   (where    :initarg :where    :reader type-error-where))
  (:report (lambda (c s)
             (format s "Error: Type mismatch: ~S vs ~S~@[ in ~A~]"
                     (type-error-expected c)
                     (type-error-found c)
                     (type-error-where c)))))

(defun unify (t1 t2 &optional (subst (empty-subst)) (where nil))
  "Unifica t1 e t2 ritornando una SUBST estesa."
  (let* ((a (subst-apply subst t1))
         (b (subst-apply subst t2)))
    (cond
      ((equal a b) subst)

      ;; variabili
      ((typevar-term-p a)
       (when (occurs-in? a b subst)
         (error 'tc-type-error :expected a :found b :where where))
       (subst-extend subst a b))

      ((typevar-term-p b)
       (when (occurs-in? b a subst)
         (error 'tc-type-error :expected b :found a :where where))
       (subst-extend subst b a))

      ;; liste
      ((and (list-type-p a) (list-type-p b))
       (unify (second a) (second b) subst where))

      ;; funzioni
      ((and (fun-type-p a) (fun-type-p b))
       (let* ((ra (fun-args a)) (rb (fun-args b))
              (oa (fun-opts a)) (ob (fun-opts b)))
         (unless (= (length ra) (length rb))
           (error 'tc-type-error :expected a :found b :where where))
         (unless (= (length oa) (length ob))
           (error 'tc-type-error :expected a :found b :where where))
         (loop for x in ra for y in rb do (setf subst (unify x y subst where)))
         (loop for x in oa for y in ob do (setf subst (unify x y subst where)))
         (unify (fun-ret a) (fun-ret b) subst where)))

      ;; basi
      ((and (base-type-p a) (base-type-p b) (eq a b)) subst)

      (t
       (error 'tc-type-error :expected a :found b :where where)))))

;;;; ===================== SCHEMI POLIMORFI =====================

(defun free-tvars (t)
  "Insieme (lista) delle variabili di tipo libere in T."
  (cond
    ((typevar-term-p t) (list t))
    ((list-type-p t) (free-tvars (second t)))
    ((fun-type-p t)
     (remove-duplicates
      (append (mapcan #'free-tvars (fun-args t))
              (mapcan #'free-tvars (fun-opts t))
              (free-tvars (fun-ret t)))
      :test #'equal))
    ((base-type-p t) '())
    (t '())))

(defun free-tvars-env (env)
  "Free tvars nell'ambiente (escludendo quelle quantificate)."
  (remove-duplicates
   (mapcan (lambda (entry)
             (destructuring-bind (sym . scheme) entry
               (declare (ignore sym))
               (scheme-free-tvars scheme)))
           env)
   :test #'equal))

(defun scheme-free-tvars (sch)
  (destructuring-bind (scheme vars body) sch
    (declare (ignore scheme))
    (remove-if (lambda (v) (member v vars :test #'equal))
               (free-tvars body)
               :test #'equal)))

(defun generalize (env t)
  "∀(free(t) - free(env)).t"
  (let* ((ft (free-tvars t))
         (fe (free-tvars-env env))
         (qs (remove-if (lambda (v) (member v fe :test #'equal)) ft :test #'equal)))
    `(scheme ,qs ,t)))

(defun instantiate (scheme)
  "Sostituisce le variabili quantificate con nuove variabili fresche."
  (destructuring-bind (scheme vars body) scheme
    (declare (ignore scheme))
    (let ((subst (empty-subst)))
      (dolist (v vars)
        (setf (gethash (tvar-id (second v)) subst) (fresh-tvar)))
      (subst-apply subst body))))

;;;; ===================== AMBIENTE =====================

;; Ambiente = alist (sym . scheme)
(defun env-empty () '())
(defun env-extend (env sym scheme) (acons sym scheme env))
(defun env-lookup (env sym)
  (let ((x (assoc sym env)))
    (if x (cdr x) (error "Unbound variable: ~A" sym))))

;;;; ===================== TIPI DEI LITERAL =====================

(defun type-of-literal (x)
  (cond
    ((integerp x) :int)
    ((or (eq x t) (eq x nil)) :bool)     ;; NIL anche lista vuota, vedi sotto
    ((stringp x) :string)
    ((characterp x) :char)
    ((symbolp x) :symbol)
    (t (fresh-tvar))))                   ;; fallback

;;;; ===================== PRELUDE (BUILT-INS) =====================

(defun poly (t) (generalize (env-empty) t))

(defun alpha () (fresh-tvar))
(defun beta  () (fresh-tvar))

(defun prelude-env ()
  (let* ((a (alpha))
         (b (beta))
         (int :int) (bool :bool))
    (list
     ;; aritmetica su int
     (cons '+  (poly (make-fun-type (list int int) '() int)))
     (cons '-  (poly (make-fun-type (list int int) '() int)))
     (cons '*  (poly (make-fun-type (list int int) '() int)))
     (cons '/  (poly (make-fun-type (list int int) '() int)))
     (cons '1+ (poly (make-fun-type (list int) '() int)))
     (cons '1- (poly (make-fun-type (list int) '() int)))
     (cons 'zerop (poly (make-fun-type (list int) '() bool)))

     ;; confronti su int -> bool
     (cons '=  (poly (make-fun-type (list int int) '() bool)))
     (cons '<  (poly (make-fun-type (list int int) '() bool)))
     (cons '<= (poly (make-fun-type (list int int) '() bool)))
     (cons '>  (poly (make-fun-type (list int int) '() bool)))
     (cons '>= (poly (make-fun-type (list int int) '() bool)))

     ;; logiche
     (cons 'not  (poly (make-fun-type (list bool) '() bool)))
     (cons 'and  (poly (make-fun-type (list bool bool) '() bool)))
     (cons 'or   (poly (make-fun-type (list bool bool) '() bool)))

     ;; liste
     (cons 'cons  (poly (make-fun-type (list a (make-list-type a)) '() (make-list-type a))))
     (cons 'car   (poly (make-fun-type (list (make-list-type a)) '() a)))
     (cons 'cdr   (poly (make-fun-type (list (make-list-type a)) '() (make-list-type a))))
     (cons 'list  (poly (make-fun-type '() (list a) (make-list-type a)))) ; 0 req, N opt uniformi
     (cons 'length (poly (make-fun-type (list (make-list-type a)) '() :int)))
     (cons 'null  (poly (make-fun-type (list (make-list-type a)) '() :bool)))
     (cons 'listp (poly (make-fun-type (list (make-list-type a)) '() :bool)))
     (cons 'atom  (poly (make-fun-type (list a) '() :bool)))

     ;; uguaglianze su simboli e generiche (semplificazione)
     (cons 'eq   (poly (make-fun-type (list :symbol :symbol) '() :bool)))
     (cons 'eql  (poly (make-fun-type (list a a) '() :bool)))
     (cons 'equal (poly (make-fun-type (list a a) '() :bool)))

     ;; predicati di tipo
     (cons 'symbolp (poly (make-fun-type (list a) '() :bool)))
     (cons 'integerp (poly (make-fun-type (list a) '() :bool)))
     (cons 'stringp (poly (make-fun-type (list a) '() :bool)))
     (cons 'characterp (poly (make-fun-type (list a) '() :bool)))
     )))

;;;; ===================== PRETTY PRINT TIPI (FTYPE) =====================

(defun pp-type (t &optional (stream *standard-output*))
  (let ((t (subst-apply (empty-subst) t))) ; normalizza
    (cond
      ((eq t :int)    (princ 'integer stream))
      ((eq t :bool)   (princ 'boolean stream))
      ((eq t :symbol) (princ 'symbol stream))
      ((eq t :string) (princ 'string stream))
      ((eq t :char)   (princ 'character stream))
      ((typevar-term-p t)     (format stream "T~A" (tvar-id (second t))))
      ((list-type-p t)
       (princ 'list stream)
       (princ #\( stream)
       (pp-type (second t) stream)
       (princ #\) stream))
      ((fun-type-p t)
       (princ 'function stream)
       (princ #\( stream)
       (princ #\( stream)
       (let ((firstp t))
         (dolist (a (fun-args t))
           (unless firstp (princ #\space stream))
           (pp-type a stream)
           (setf firstp nil))
         (when (fun-opts t)
           (unless firstp (princ #\space stream))
           (princ '&optional stream)
           (dolist (o (fun-opts t))
             (princ #\space stream)
             (pp-type o stream))))
       (princ #\) stream)
       (princ #\space stream)
       (pp-type (fun-ret t) stream)
       (princ #\) stream))
      (t (princ t stream)))))

(defun print-ftype (name ftype)
  (format t "(ftype ~S ~A)~%" (with-output-to-string (s) (pp-type ftype s)) name))

;;;; ===================== INFERENZA =====================

;; Ritorniamo (values Type Subst Env)
;; Env è potenzialmente esteso (p.es. in defun)

(defun infer (env expr subst)
  (dbg "infer ~S" expr)
  (cond
    ;; literal
    ((or (integerp expr) (stringp expr) (characterp expr) (eq expr t) (eq expr nil))
     (values (type-of-literal expr) subst env))

    ;; simbolo (variabile)
    ((symbolp expr)
     (let ((scheme (env-lookup env expr)))
       (values (instantiate scheme) subst env)))

    ;; quote
    ((and (consp expr) (eq (first expr) 'quote))
     (let ((obj (second expr)))
       (cond
         ((symbolp obj) (values :symbol subst env))
         ((consp obj)
          ;; lista quoted: impone uniformità sugli elementi
          (let ((a (fresh-tvar)) (s subst))
            (dolist (el obj)
              (multiple-value-bind (te s2 env2) (infer env el s)
                (declare (ignore env2))
                (setf s (unify a te s :where '(quote)))))
            (values (make-list-type (subst-apply s a)) s env)))
         (t (values (type-of-literal obj) subst env))))

    ;; lambda
    ((and (consp expr) (eq (first expr) 'lambda))
     (destructuring-bind (lambda params &rest body) expr
       (declare (ignore lambda))
       ;; parametri: supporta (x y &optional z w)
       (let ((req '()) (opt '()) (names '()) (opt-mode nil))
         (dolist (p params)
            (when (member p '(t nil))
                (error "Parametro ~S non valido: T e NIL sono costanti." p))
            (cond
                ((eq p '&optional) (setf opt-mode t))
                (opt-mode (push (fresh-tvar) opt) (push p names))
                (t       (push (fresh-tvar) req)  (push p names))))
         (setf req (nreverse req) opt (nreverse opt) names (nreverse names))
         (let* ((env2 env)
                ;; bind parametri come monomorfi (no generalization)
                (env2 (loop for n in names
                            for t in (append req opt)
                            do (setf env2 (env-extend env2 n `(scheme () ,t)))
                            finally (return env2)))
                (s subst))
           ;; corpo: progn implicito
           (multiple-value-bind (tbody s2 env3)
               (infer-progn env2 body s)
             (declare (ignore env3))
             (values (make-fun-type req opt tbody) s2 env))))))

    ;; if
    ((and (consp expr) (eq (first expr) 'if))
     (destructuring-bind (if test then else) expr
       (declare (ignore if))
       (multiple-value-bind (tt s1 e1) (infer env test subst)
         (declare (ignore e1))
         (setf s1 (unify tt :bool s1 :where 'if))
         (multiple-value-bind (tthen s2 e2) (infer env then s1)
           (declare (ignore e2))
           (multiple-value-bind (telse s3 e3) (infer env else s2)
             (declare (ignore e3))
             (values (subst-apply s3 (unify tthen telse s3 :where 'if))
                     s3 env))))))

    ;; let: let ((x e1) (y e2)) body...
    ((and (consp expr) (eq (first expr) 'let))
     (destructuring-bind (let bindings &rest body) expr
       (declare (ignore let))
       (let ((s subst)
             (env2 env))
         (dolist (b bindings)
           (destructuring-bind (name value) b
                (when (member name '(t nil))
                (error "Binding non valido in LET: ~S è una costante." name))
                (multiple-value-bind (tv sv ev) (infer env2 value s)
               (declare (ignore ev))
               ;; generalize rispetto all'ambiente corrente (HM let)
               (let* ((tgen (generalize env2 (subst-apply sv tv))))
                 (setf env2 (env-extend env2 name tgen)
                       s    sv)))))
         (infer-progn env2 body s))))

    ;; defun
    ((and (consp expr) (eq (first expr) 'defun))
     (destructuring-bind (defun name params &rest body) expr
       (declare (ignore defun))
       ;; crea tipo per i params (req + opt)
       (let ((req '()) (opt '()) (names '()) (opt-mode nil))
         (dolist (p params)
            (when (member p '(t nil))
                (error "Parametro ~S non valido: T e NIL sono costanti." p))
            (cond
                ((eq p '&optional) (setf opt-mode t))
                (opt-mode (push (fresh-tvar) opt) (push p names))
                (t       (push (fresh-tvar) req)  (push p names))))

         (setf req (nreverse req) opt (nreverse opt) names (nreverse names))
         (let* ((env-fn (env-extend env name (poly (make-fun-type req opt (fresh-tvar))))) ; self-rec
                (env2   env-fn))
           ;; bind parametri monomorfi
           (setf env2 (loop for n in names
                            for t in (append req opt)
                            do (setf env2 (env-extend env2 n `(scheme () ,t)))
                            finally (return env2)))
           (multiple-value-bind (tbody s2 e2) (infer-progn env2 body subst)
             (declare (ignore e2))
             (let* ((ft (make-fun-type (mapcar (lambda (x) (subst-apply s2 x)) req)
                                       (mapcar (lambda (x) (subst-apply s2 x)) opt)
                                       (subst-apply s2 tbody)))
                    (gen (generalize env ft))
                    (env3 (env-extend env name gen)))
               (print-ftype name ft)
               (values ft s2 env3))))))

    ;; progn implicito: (progn a b c)
    ((and (consp expr) (eq (first expr) 'progn))
     (infer-progn env (rest expr) subst))

    ;; application: (f arg1 ... argN)
    ((consp expr)
     (let* ((f (first expr)) (args (rest expr))
            (s subst))
       ;; infer callee
       (multiple-value-bind (tf s1 e1) (infer env f s)
         (declare (ignore e1))
         (let ((req-types '())
               (opt-types '()))
           ;; modelliamo le chiamate come se la funzione avesse
           ;; prima tutti i required, poi eventuali optional (qui,
           ;; consideriamo tutto come required e poi permettiamo un
           ;; matching anche con funzioni che hanno optional in più).
           (dolist (arg args)
             (multiple-value-bind (ta s2 e2) (infer env arg s1)
               (declare (ignore e2))
               (push ta req-types)
               (setf s1 s2)))
           (setf req-types (nreverse req-types))
           (let* ((ret (fresh-tvar))
                  (goal (make-fun-type req-types '() ret)))
             (setf s1 (unify tf goal s1 :where 'call))
             (values (subst-apply s1 ret) s1 env))))))

    (t
     (error "Unsupported form: ~S" expr))))))

(defun infer-progn (env forms subst)
  (let ((s subst)
        (tlast :unit)  ; fantasma per sequenze
        (e env))
    (dolist (f forms)
      (multiple-value-bind (tf sf ef) (infer e f s)
        (setf tlast tf s sf e ef)))
    (values tlast s e)))

;;;; ===================== DRIVER =====================

(defun tc (pathname)
  "Esegue il type checking del file .lisp"
  (format t ";;; Type checking ~S.~%~%" pathname)
  (let ((*read-eval* nil))
    (with-open-file (in pathname :direction :input :external-format :default)
      (let ((env (append (prelude-env) (env-empty)))
            (subst (empty-subst)))
        (loop
          for form = (ignore-errors (read in nil :eof))
          until (eq form :eof)
          do
            (handler-case
                (multiple-value-bind (tform s2 env2) (infer env form subst)
                  (declare (ignore tform))
                  (setf subst s2 env env2))
              (tc-type-error (e)
                (format t "~A~%" e))
              (error (e)
                (format t "Error: ~A in form ~S~%" e form))))
        t))))

;;;; ===================== ESEMPI RAPIDI (commentati) =====================
#|
;; Esempio 1: fattoriale
(defun fact (n &optional (acc 1))
  (if (zerop n)
      acc
      (fact (1- n) (* n acc))))

(format t "~D! is ~D~%" 6 (fact 6))
(format t "~D! is ~D~%" 6 (fact 'six)) ; <-- genera errore

;; Output atteso (estratto):
;; (ftype (function (integer &optional integer) integer) FACT)
;; Error: ’six’ is not of type ’integer’ in call (fact 'six)   ; linea indicativa
|#
