;;;; 889018 Biglioli Sabrina
;;;; 917356 Carducci Lorenzo
;;;; 914396 Coletta Giovanni

;;;; Type checker minimale per Common Lisp in Common Lisp
;;;; (Hindley-Milner style per un piccolo sottoinsieme di CL)


;;;; ============================================================
;;;; ERRORI DEL TYPE CHECKER (NO DEBUGGER)
;;;; ============================================================
(define-condition tc-error (error)
    "Stampa errore personalizzato per il type checker."
    ((msg :initarg :msg :reader tc-error-msg))
    (:report (lambda (c stream)
                (format stream "~A" (tc-error-msg c)))))

(defun tc-signal-error (fmt &rest args)
    "Segnala un errore di type checking."
    (error 'tc-error :msg (apply #'format nil fmt args)))


;;;; ============================================================
;;;; RAPPRESENTAZIONE DEI TIPI
;;;; ============================================================
;; Definisco come rappresento i vari tipi nel mio type checker.
;; Tipi interni:
;;   (:int)                       -> integer
;;   (:bool)                      -> boolean
;;   (:string)                    -> string
;;   (:sym)                       -> symbol
;;   (:list T)                    -> (list T)
;;   (:var ID)                    -> variabile di tipo
;;   (:fun REQ OPT RET)           -> funzione (REQ args obbligatori, OPT args opzionali)

(defun int-type () '(:int))
(defun bool-type () '(:bool))
(defun string-type () '(:string))
(defun sym-type () '(:sym))
(defun list-type (elem) (list :list elem))
(defun var-type (id) (list :var id))
(defun fun-type (req opt ret) (list :fun req opt ret))

(defun type-var-p (ty)
  (and (consp ty) (eq (first ty) :var)))

(defun list-type-p (ty)
  (and (consp ty) (eq (first ty) :list)))

(defun fun-type-p (ty)
  (and (consp ty) (eq (first ty) :fun)))


;;;; ============================================================
;;;; SCHEMI DI TIPO E AMBIENTE
;;;; ============================================================
;; Definisco come rappresento gli schemi di tipo e l’ambiente
;; che associa i nomi delle funzioni/variabili ai loro tipi.
;; Uno schema rappresenta un tipo con variabili quantificate:
;; (:scheme VARS TYPE) dove VARS è una lista di ID di variabili di tipo quantificate.

(defun make-scheme (vars type)
  (list :scheme vars type))

(defun scheme-vars (sch) (second sch))
(defun scheme-type (sch) (third sch))

(defun env-empty () nil)

(defun env-extend (env name scheme)
  (acons name scheme env))

(defun env-lookup (env name)
  (let ((cell (assoc name env)))
    (when cell (cdr cell))))


;;;; ============================================================
;;;; SOSTITUZIONI (per le variabili di tipo)
;;;; ============================================================
;; Gestisco le sostituzioni per le variabili di tipo e l’unificazione
;; dei tipi usando una sostituzione globale.

(defparameter *subst* nil)          
(defparameter *next-type-var-id* 0)

(defun fresh-type-var ()
  "Crea una nuova variabile di tipo."
  (incf *next-type-var-id*)
  (var-type *next-type-var-id*))

(defun lookup-subst (id)
  (assoc id *subst*))

(defun occurs-in-type-p (id type)
  "Occurs check: verifica se la var di tipo ID compare in TYPE."
  (cond
    ((type-var-p type)
     (let* ((tid (second type))
            (binding (lookup-subst tid)))
       (if binding
           (occurs-in-type-p id (cdr binding))
           (= id tid))))
    ((list-type-p type)
     (occurs-in-type-p id (second type)))
    ((fun-type-p type)
     (or (some (lambda (ty) (occurs-in-type-p id ty)) (second type))
         (some (lambda (ty) (occurs-in-type-p id ty)) (third type))
         (occurs-in-type-p id (fourth type))))
    (t nil)))

(defun apply-subst (type)
  "Applica la sostituzione globale *SUBST* a TYPE."
  (cond
    ((type-var-p type)
     (let* ((id (second type))
            (binding (lookup-subst id)))
       (if binding
           (apply-subst (cdr binding))
           type)))
    ((list-type-p type)
     (list-type (apply-subst (second type))))
    ((fun-type-p type)
     (fun-type (mapcar #'apply-subst (second type))
               (mapcar #'apply-subst (third type))
               (apply-subst (fourth type))))
    (t type)))

(defun unify-var (id type)
  "Unifica la var di tipo ID con TYPE."
  (let ((binding (lookup-subst id)))
    (cond
      (binding
       (unify (cdr binding) type))
      ((and (type-var-p type)
            (= id (second type)))
       type)
      ((occurs-in-type-p id type)
       (tc-signal-error "Occurs check failed: ~A in ~A" (var-type id) type))
      (t
       (push (cons id type) *subst*)
       type))))

(defun unify (t1 t2)
  "Unificazione dei tipi (modifica *SUBST*)."
  (setf t1 (apply-subst t1)
        t2 (apply-subst t2))
  (cond
    ((and (type-var-p t1) (type-var-p t2)
          (= (second t1) (second t2)))
     t1)
    ((type-var-p t1)
     (unify-var (second t1) t2))
    ((type-var-p t2)
     (unify-var (second t2) t1))
    ((and (list-type-p t1) (list-type-p t2))
     (unify (second t1) (second t2)))
    ((and (fun-type-p t1) (fun-type-p t2))
     (let* ((req1 (second t1))
            (opt1 (third t1))
            (ret1 (fourth t1))
            (req2 (second t2))
            (opt2 (third t2))
            (ret2 (fourth t2)))
       (unless (and (= (length req1) (length req2))
                    (= (length opt1) (length opt2)))
         (tc-signal-error "Cannot unify function types (different arity): ~A vs ~A" t1 t2))
       (mapc #'unify req1 req2)
       (mapc #'unify opt1 opt2)
       (unify ret1 ret2)))
    ((equal t1 t2)
     t1)
    (t
     (tc-signal-error "Type mismatch: ~A vs ~A" t1 t2))))


;;;; ============================================================
;;;; INSIEMI DI VARIABILI DI TIPO
;;;; ============================================================
;; Calcolo le variabili di tipo libere in tipi, schemi e ambiente,
;; e gestisco generalizzazione e istanziazione degli schemi.

(defun ftv-type (type)
  "Restituisce le variabili di tipo libere presenti in TYPE (come lista di ID)."
  (cond
    ((type-var-p type)
     (list (second type)))
    ((list-type-p type)
     (ftv-type (second type)))
    ((fun-type-p type)
     (union (mapcan #'ftv-type (second type))
            (union (mapcan #'ftv-type (third type))
                   (ftv-type (fourth type)))))
    (t nil)))

(defun ftv-scheme (scheme)
  "Restituisce le variabili di tipo libere di uno schema."
  (let* ((vars (scheme-vars scheme))
         (tvars (ftv-type (scheme-type scheme))))
    (set-difference tvars vars)))

(defun ftv-env (env)
  "Restituisce le variabili di tipo libere presenti nell'ambiente ENV."
  (remove-duplicates
   (mapcan (lambda (entry)
             (ftv-scheme (cdr entry)))
           env)))

(defun generalize (env type)
  "Generalizza TYPE rispetto all'ENV."
  (let* ((tvars (ftv-type type))
         (env-vars (ftv-env env))
         (vars (set-difference tvars env-vars)))
    (make-scheme vars type)))

(defun tsubst-with (type subst)
  "Applica una sostituzione locale SUBST a TYPE."
  (cond
    ((type-var-p type)
     (let* ((id (second type))
            (binding (assoc id subst)))
       (if binding
           (tsubst-with (cdr binding) subst)
           type)))
    ((list-type-p type)
     (list-type (tsubst-with (second type) subst)))
    ((fun-type-p type)
     (fun-type (mapcar (lambda (ty) (tsubst-with ty subst)) (second type))
               (mapcar (lambda (ty) (tsubst-with ty subst)) (third type))
               (tsubst-with (fourth type) subst)))
    (t type)))

(defun instantiate (scheme)
  "Istanzia uno schema con nuove variabili di tipo."
  (let* ((vars (scheme-vars scheme))
         (subst (mapcar (lambda (v) (cons v (fresh-type-var))) vars)))
    (tsubst-with (scheme-type scheme) subst)))


;;;; ============================================================
;;;; PRETTY PRINT DEI TIPI (stile Common Lisp)
;;;; ============================================================
;; Converto i tipi interni in una forma leggibile in stile Common Lisp
;; e formatto sia i tipi sia le espressioni per la stampa dei messaggi.

(defun type->cl-type (type)
  "Converte il tipo interno in una 'CL type specifier' simbolica."
  (setf type (apply-subst type))
  (cond
    ((equal type (int-type)) 'integer)
    ((equal type (bool-type)) 'boolean)
    ((equal type (string-type)) 'string)
    ((equal type (sym-type)) 'symbol)
    ((list-type-p type)
     `(list ,(type->cl-type (second type))))
    ((fun-type-p type)
     (let* ((req (mapcar #'type->cl-type (second type)))
            (opt (mapcar #'type->cl-type (third type)))
            (ret (type->cl-type (fourth type)))
            (arg-list (if opt
                          (append req (list '&optional) opt)
                          req)))
       `(function ,arg-list ,ret)))
    ((type-var-p type)
     ;; per debugging: Tn
     (intern (format nil "T~A" (second type))))
    (t
     type)))

(defun expr->string (expr)
  "Restituisce una rappresentazione leggibile dell'espressione,
   usando l'abbreviazione 'x per (quote x) e simboli in minuscolo."
  (labels ((pp (e)
             (cond
               ;; 'x
               ((and (consp e)
                     (eq (first e) 'quote)
                     (symbolp (second e)))
                (format nil "'~(~A~)" (second e)))
               ;; liste generiche: (f a b ...)
               ((consp e)
                (format nil "(~{~A~^ ~})"
                        (mapcar #'pp e)))
               ;; simboli: minuscoli
               ((symbolp e)
                (format nil "~(~A~)" e))
               ;; numeri, stringhe, ecc.
               (t
                (prin1-to-string e)))))
    (pp expr)))

(defun type->name-string (type)
  "Restituisce il nome del tipo in stile Common Lisp."
  (let* ((*print-case* :downcase)
         (cl-ty (type->cl-type (apply-subst type))))
    (format nil "~A" cl-ty)))

(defun print-function-type (name fun-ty)
  "Stampa (ftype (function ...) name)"
  (let ((cl-ty (type->cl-type fun-ty)))
    (destructuring-bind (fn-keyword arglist ret) cl-ty
      (declare (ignore fn-keyword))
      (format t "~&(ftype (function ~S ~S) ~S)~%"
              arglist ret name))))


;;;; ============================================================
;;;; AMBIENTE DI BASE (PRIMITIVE)
;;;; ============================================================
;; Costruisco l’ambiente iniziale, cioè i tipi delle primitive
;; aritmetiche e logiche di Lisp che il type checker deve conoscere.

(defun initial-env ()
  "Ambiente iniziale con alcune primitive."
  (let ((env (env-empty)))
    ;; integer literals, ecc. sono gestiti direttamente
    ;; zerop : integer -> boolean
    (setf env (env-extend env 'zerop
                          (make-scheme nil
                                       (fun-type (list (int-type)) 
                                                 nil 
                                                 (bool-type)))))
    ;; 1-   : integer -> integer
    (setf env (env-extend env '1-
                          (make-scheme nil
                                       (fun-type (list (int-type)) 
                                                 nil 
                                                 (int-type)))))
    ;; + : integer integer -> integer
    (setf env (env-extend env '+
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (int-type)))))
    ;; - : integer integer -> integer
    (setf env (env-extend env '-
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (int-type)))))
    ;; * : integer integer -> integer
    (setf env (env-extend env '*
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (int-type)))))
    ;; / : integer integer -> integer
    (setf env (env-extend env '/
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (int-type)))))
    ;; = : integer integer -> boolean
    (setf env (env-extend env '=
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (bool-type)))))
    ;; /= : integer integer -> boolean
    (setf env (env-extend env '/=
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (bool-type)))))
    ;; < : integer integer -> boolean
    (setf env (env-extend env '<
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (bool-type)))))
    ;; <= : integer integer -> boolean
    (setf env (env-extend env '<=
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (bool-type)))))
    ;; > : integer integer -> boolean
    (setf env (env-extend env '>
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (bool-type)))))
    ;; >= : integer integer -> boolean
    (setf env (env-extend env '>=
                          (make-scheme nil
                                       (fun-type (list (int-type) (int-type))
                                                 nil
                                                 (bool-type)))))
    ;; format: non facciamo type checking sugli argomenti
    (let* ((tvar (fresh-type-var))
           (fmt-ty (fun-type (list (string-type))
                             nil
                             tvar)))
      (setf env (env-extend env 'format
                            (make-scheme (ftv-type fmt-ty) fmt-ty))))
    env))


;;;; ============================================================
;;;; INFERENZA DEI TIPI PER ESPRESSIONI
;;;; ============================================================
;; Implemento la parte del type checker che prova a
;; indovinare il tipo delle espressioni Lisp a partire dalla loro forma:
;; numeri, stringhe, simboli, quote, if e chiamate di funzione (con
;; alcuni casi speciali per macro, handler-case, format e funzioni del
;; Lisp host).

(defun infer-symbol (sym env)
  (cond
    ;; booleani
    ((or (eq sym 't) (eq sym 'nil))
     (bool-type))

    ;; keyword: le trattiamo come simboli costanti
    ((keywordp sym)
     (sym-type))

    ;; variabili globali del tipo *foo*: le consideriamo ben tipate,
    ;; ma senza controllarne davvero il tipo
    ((let* ((name (symbol-name sym))
            (len  (length name)))
       (and (> len 1)
            (char= (char name 0) #\*)
            (char= (char name (1- len)) #\*)))
     (fresh-type-var))

    (t
     (let ((scheme (env-lookup env sym)))
       (unless scheme
         (tc-signal-error "Unbound symbol ~S" sym))
       (instantiate scheme)))))


(defun infer-quote (form env)
  (declare (ignore env))
  ;; '(...) -> lista, 'simbolo -> symbol
  (let ((obj (second form)))
    (cond
      ((symbolp obj) (sym-type))
      ((numberp obj) (int-type))
      ((stringp obj) (string-type))
      ((consp obj)   (list-type (fresh-type-var)))
      (t (fresh-type-var)))))

(defun infer-if (form env)
  ;; form = (if test then [else])
  (let ((test (second form))
        (then (third form))
        (else (fourth form)))
    (unless (and test then)
      (tc-signal-error "Malformed IF: ~A" (expr->string form)))
    (let ((t-ty (infer-expr test env)))
      (unify t-ty (bool-type)))
    (let ((then-ty (infer-expr then env))
          (else-ty (if else
                       (infer-expr else env)
                       (bool-type))))
      (unify then-ty else-ty)
      then-ty)))


(defun fun-type-required (fun-ty) (second fun-ty))
(defun fun-type-optional (fun-ty) (third fun-ty))
(defun fun-type-ret (fun-ty) (fourth fun-ty))

(defun infer-call (form env)
  "Inferenza per una chiamata di funzione (f arg1 arg2 ...)."
  (block infer-call
    (let* ((fn   (first form))
           (args (rest form)))

      ;; -------------------------------------------------------
      ;; Se l'operatore non è un simbolo → NON è una chiamata
      ;; di funzione, ma una struttura-dato.
      ;; Type-checking solo per i sottoform che sono liste.
      ;; -------------------------------------------------------

      ;; 1) operatore non simbolo → struttura dati, non funzione
      (unless (symbolp fn)
        (dolist (sf args)
          (when (consp sf)
            (infer-expr sf env)))
        (return-from infer-call (fresh-type-var)))

      ;; 2) operatore keyword → opzione tipo :report
      (when (keywordp fn)
        (dolist (sf args)
          (when (and (consp sf) (eq (first sf) 'lambda))
            (infer-expr sf env)))
        (return-from infer-call (fresh-type-var)))

      ;; 3) CASO SPECIALE: DEFINE-CONDITION
      ;; trattiamo solo le lambda dentro alle opzioni, il resto è dato
      (when (eq fn 'define-condition)
        (dolist (sf args)
          (when (and (consp sf) (eq (first sf) 'lambda))
            (infer-expr sf env)))
        (return-from infer-call (fresh-type-var)))

      ;; -------------------------------------------------------
      ;; CASO SPECIALE: HANDLER-CASE
      ;; -------------------------------------------------------
      (when (eq fn 'handler-case)
        (let ((protected (first args))
              (clauses   (rest args)))
          ;; espressione protetta
          (infer-expr protected env)
          ;; per ogni clausola, ignoriamo nome condition e binding,
          ;; e verifichiamo solo i body
          (dolist (clause clauses)
            (when (consp clause)
              (destructuring-bind (cond-type bindings &rest body) clause
                (declare (ignore cond-type bindings))
                (infer-progn body env))))
          (return-from infer-call (fresh-type-var))))

      ;; -------------------------------------------------------
      ;; CASO GENERICO: macro o special form del Lisp host
      ;; Esempi: define-condition, when, unless, and, or, ...
      ;; Analizziamo SOLO i sottoform che sono liste.
      ;; -------------------------------------------------------
      (when (or (special-operator-p fn)
                (macro-function fn))
        (dolist (sf args)
          (when (consp sf)
            (infer-expr sf env)))
        (return-from infer-call (fresh-type-var)))

      ;; -------------------------------------------------------
      ;; CASO SPECIALE: FORMAT
      ;; Non controlliamo arità/tipo di FORMAT, ma analizziamo
      ;; comunque tutti gli argomenti.
      ;; -------------------------------------------------------
      (when (eq fn 'format)
        (dolist (a args)
          (infer-expr a env))
        (return-from infer-call (fresh-type-var)))

      ;; -------------------------------------------------------
      ;; CASO GENERALE: vera funzione (nostra o del CL host)
      ;; -------------------------------------------------------
      (let ((scheme (env-lookup env fn)))
        ;; Se non è nel nostro env ma è una funzione definita nel CL host
        ;; la trattiamo come "esterna":
        ;; checkiamo solo gli argomenti, ignorando tipo/aritá della funzione.
        (unless scheme
          (when (fboundp fn)
            (dolist (a args)
              (infer-expr a env))
            (return-from infer-call (fresh-type-var)))
          (tc-signal-error "Unknown function ~S" fn))

        ;; Qui FN è una nostra funzione con tipo noto
        (let* ((fun-ty    (instantiate scheme))
               (req       (fun-type-required fun-ty))
               (opt       (fun-type-optional fun-ty))
               (ret       (fun-type-ret fun-ty))
               (min-arity (length req))
               (max-arity (+ min-arity (length opt)))
               (n-args    (length args)))
          (when (or (< n-args min-arity) (> n-args max-arity))
            (tc-signal-error
             "Arity mismatch in call ~A: expected ~D-~D args, got ~D"
             (expr->string form) min-arity max-arity n-args))
          ;; unifichiamo argomenti; in caso di errore, stampiamo il messaggio formattato
          (let ((param-types (append req opt)))
            (loop for arg in args
                  for pty in param-types
                  do
                    (let ((aty (infer-expr arg env)))
                      (handler-case
                          (unify pty aty)
                        (tc-error (c)
                          (declare (ignore c))
                          (let* ((expected-str (type->name-string pty))
                                 (arg-str      (expr->string arg))
                                 (call-str     (expr->string form)))
                            (tc-signal-error
                             "'~A' is not of type '~A' in call ~A"
                             arg-str expected-str call-str)))))))
          (apply-subst ret))))))


(defun infer-expr (expr env)
  "Inferenza del tipo di una generica espressione."
  (cond
    ((numberp expr) (int-type))
    ((stringp expr) (string-type))
    ((symbolp expr) (infer-symbol expr env))
    ((consp expr)
     (case (first expr)
       (quote  (infer-quote expr env))
       (if     (infer-if expr env))
       (t      (infer-call expr env))))
    (t
     (fresh-type-var))))

(defun infer-progn (forms env)
  "Valuta ogni espressione e restituisce il tipo dell'ultima della lista."
  (let ((result-type (bool-type)))
    (dolist (f forms)
      (setf result-type (infer-expr f env)))
    result-type))


;;;; ============================================================
;;;; INFERENZA PER DEFUN (top-level)
;;;; ============================================================
;; Gestisco le DEFUN di top-level: analizzo la lista di parametri,
;; assegno variabili di tipo agli argomenti e al valore di ritorno,
;; inferisco il tipo del corpo (supportando la ricorsione) e
;; aggiorno l'ambiente con il tipo della funzione.

(defun parse-parameter-list (params)
  "Restituisce (req-names opt-specs)
   req-names : lista di simboli obbligatori
   opt-specs : lista di (name default-expr | name)"
  (let ((req '())
        (opt '())
        (mode :req))
    (dolist (p params)
      (cond
        ((eq p '&optional) (setf mode :opt))
        ((eq mode :req)
         (push p req))
        (t
         (push p opt))))
    (values (nreverse req) (nreverse opt))))

(defun infer-defun (form env)
  "Inferisce il tipo di una funzione definita con DEFUN e
   restituisce (values new-env function-type)."
  (destructuring-bind (_ name params &rest body) form
    (declare (ignore _))
    (multiple-value-bind (req-names opt-specs) (parse-parameter-list params)
      ;; creiamo le variabili di tipo per parametri e ritorno
      (let* ((req-types (mapcar (lambda (_x) (fresh-type-var)) req-names))
             (opt-types (mapcar (lambda (_x) (fresh-type-var)) opt-specs))
             (ret-type (fresh-type-var))
             (fun-ty   (fun-type req-types opt-types ret-type)))
        ;; ambiente con la funzione stessa (ricorsione)
        (let* ((fun-scheme (make-scheme nil fun-ty))
               (env-with-fun (env-extend env name fun-scheme))
               ;; ambiente con parametri
               (env-with-params
                 (let ((e env-with-fun))
                   ;; parametri obbligatori
                   (loop for pname in req-names
                         for pty   in req-types
                         do (setf e (env-extend e pname (make-scheme nil pty))))
                   ;; parametri opzionali
                   (loop for p in opt-specs
                         for pty in opt-types
                         do (let ((pname (if (consp p) (first p) p)))
                              (setf e (env-extend e pname (make-scheme nil pty)))))
                   e)))
          ;; Unifichiamo i tipi dei default delle opzionali, se presenti
          (loop for p in opt-specs
                for pty in opt-types
                do (when (consp p)
                     (let ((default-expr (second p)))
                       (unify pty (infer-expr default-expr env-with-params)))))
          ;; Tipo del corpo
          (let ((body-type (infer-progn body env-with-params)))
            (unify ret-type body-type)
            (let* ((generalized-fun-type (apply-subst fun-ty))
                   (scheme (generalize env generalized-fun-type))
                   (new-env (env-extend env name scheme)))
              (values new-env generalized-fun-type))))))))


;;;; ============================================================
;;;; FUNZIONE PRINCIPALE: (tc "file.lisp")
;;;; ============================================================
;; Funzione principale del type checker: legge il file e controlla i tipi di ogni forma top-level.
;; Stampa i tipi delle funzioni o gli eventuali errori.

(defun process-top-form (form env)
  "Processa una forma top-level. Restituisce il nuovo env."
  (cond
    ;; defun: inferiamo il tipo e lo stampiamo
    ((and (consp form) (eq (first form) 'defun))
     (multiple-value-bind (new-env fun-ty) (infer-defun form env)
       (print-function-type (second form) fun-ty)
       new-env))
    ;; altre forme: errori
    (t
     (infer-expr form env)
     env)))

(defun tc (filename)
  "Funzione principale del Type checker."
  (format t ";;; Type checking '~A'.~%~%" filename)
  (let ((*subst* nil)
        (*next-type-var-id* 0)
        (*print-case* :downcase)
        (*print-pretty* t))
    (let ((env (initial-env)))
      (with-open-file (in filename :direction :input)
  
        (loop for form = (read in nil :eof)
              until (eq form :eof)
              do
                (handler-case
                    (setf env (process-top-form form env))
                  (tc-error (c)
                    (format t "Error: ~A~%" (tc-error-msg c)))
                  (error (c)
                    ;; errori imprevisti: li segnaliamo ma continuiamo
                    (format t "Internal error: ~A~%" c))))))
    t))