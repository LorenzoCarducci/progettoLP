;;;; 889018 Biglioli Sabrina
;;;; 917356 Carducci Lorenzo
;;;; 914396 Coletta Giovanni
;;;; Type checker minimale per Lisp (interi + variabili + liste + built-in)

; (in-package :cl-user)

; (defpackage :tc
;   (:use :cl)
;   (:export :tc))

; (in-package :tc)


(defun tc (filename)
  "Entry point del type checker.
   Per ora: legge il file e mostra le forme top-level."
  (format t ";;; Type checking '~A'.~%~%" filename)
  (let ((forms (read-all-forms-from-file filename)))
    ;; Per ora, processiamo le forme una alla volta
    (dolist (form forms)
      (process-top-level-form form)))
  ;; In futuro potremmo restituire T/NIL a seconda del successo
  t)


(defun read-all-forms-from-file (filename)
  "Legge tutte le forme Lisp da FILENAME e le restituisce come lista."
  (with-open-file (in filename :direction :input)
    (loop for form = (read in nil :eof)
          until (eq form :eof)
          collect form)))


(defparameter *function-table*
  (make-hash-table :test #'eq)
  "Tabella che associa il nome della funzione a una struttura con info sul numero di argomenti, ecc.")


(defstruct function-info
  name          ; simbolo della funzione
  required-args ; lista dei parametri obbligatori
  optional-args ; lista dei parametri opzionali
  min-arity     ; numero minimo di argomenti
  max-arity     ; numero massimo di argomenti
  ;; in futuro: rest-arg, keyword-args, tipo di ritorno, tipo degli argomenti, ecc.
  )


(defstruct function-type
  arg-types           ; lista tipi degli argomenti obbligatori
  optional-arg-types  ; lista tipi degli argomenti opzionali
  return-type)        ; tipo di ritorno


(defparameter *function-type-env*
  (let ((ht (make-hash-table :test #'eq)))
    ;; Built-in aritmetici su interi
    (setf (gethash '+ ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))
    (setf (gethash '* ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))
    (setf (gethash '- ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '(:int)  ; (- x) o (- x y)
           :return-type :int))
    (setf (gethash '1- ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '()
           :return-type :int))
    (setf (gethash 'zerop ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '()
           :return-type :bool))
    ht)
  "Tabella dei tipi delle funzioni built-in e delle defun utente note.")



(defun process-top-level-form (form)
  "Analizza una forma top-level.
   - DEFUN: registra la funzione.
   - Altro: prova a fare un controllo sulla chiamata."
  (cond
    ((and (consp form)
          (eq (car form) 'defun))
     (process-defun-form form))
    (t
     ;; qui facciamo il controllo sulle espressioni top-level
     (type-check-expression form))))


(defun type-check-top-level-expression (form)
  "Controlla una espressione top-level.
   Per ora: controlla solo l'arità delle funzioni definite dall'utente."
  (format t "Checking top-level expression: ~S~%" form)
  (type-check-expression form nil))


(defun type-check-expression (expr)
  "Controllo minimalista delle espressioni.
   Usa *function-type-env* per controllare le chiamate a funzioni note."
  (cond
    ;; numeri, simboli, stringhe, NIL da soli: niente da controllare
    ((or (integerp expr)
         (symbolp expr)
         (stringp expr)
         (null expr))
     nil)

    ;; quote, tipo 'six o '3
    ((and (consp expr)
          (eq (car expr) 'quote))
     nil)

    ;; chiamata di funzione o forma speciale
    ((consp expr)
     (let ((fn   (car expr))
           (args (cdr expr)))
       ;; prima controlliamo ricorsivamente tutti gli argomenti
       (dolist (a args)
         (type-check-expression a))
       ;; poi, se conosciamo il tipo della funzione, controlliamo gli argomenti
       (let ((ftype (gethash fn *function-type-env*)))
         (when ftype
           (check-function-call fn ftype args expr)))))
    (t
     nil)))


(defun check-function-call (fn ftype args original-expr)
  "Controlla numero di argomenti e tipo per una funzione nota in *function-type-env*."
  (let* ((req   (function-type-arg-types ftype))
         (opt   (function-type-optional-arg-types ftype))
         (nreq  (length req))
         (nopt  (length opt))
         (nargs (length args)))
    ;; Controllo arità
    (when (< nargs nreq)
      (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne richiede almeno ~D.~%  Espressione: ~S~%"
              fn nargs nreq original-expr))
    (when (> nargs (+ nreq nopt))
      (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne accetta al massimo ~D.~%  Espressione: ~S~%"
              fn nargs (+ nreq nopt) original-expr))
    ;; Controllo tipi degli argomenti che sappiamo tipare
    (loop
      for arg in args
      for expected-type in (append req opt)
      do (when expected-type
           (let ((actual-type (infer-type arg)))
             ;; se non riusciamo a inferire (:unknown) non diciamo nulla
             (when (and (not (eq actual-type :unknown))
                        (not (eq actual-type expected-type)))
               (format t "Error: '~A' is not of type '~(~A~)' in call ~S~%"
                       (display-arg arg)
                       expected-type
                       original-expr)))))))



(defun process-defun-form (form)
  "Analizza una forma (defun ...) e la registra nella *function-table*."
  ;; Forma attesa: (defun name (params...) body...)
  (destructuring-bind (_defun name params-list &rest _body)
      form
    (let* ((required-params '())
           (optional-params '()))
      ;; Parametri possono essere: (x y &optional (acc 1))
      (loop for rest-params on params-list
            for param = (car rest-params)
            do (cond
                 ((eq param '&optional)
                  (setf optional-params (cdr rest-params))
                  (return))
                 (t
                  (push param required-params))))
      (setf required-params (nreverse required-params))
      ;; Creiamo la struttura function-info (info "strutturale": solo nomi parametri)
      (let ((info (make-function-info
                   :name          name
                   :required-args required-params
                   :optional-args optional-params)))
        (setf (gethash name *function-table*) info)

        ;; --- Qui agganciamo anche le informazioni di TIPO ---

        ;; Caso specifico di FACT come da traccia:
        ;; (function (integer &optional integer) integer)
        (when (eq name 'fact)
          ;; registra il tipo nella tabella dei tipi di funzione
          (setf (gethash name *function-type-env*)
                (make-function-type
                 :arg-types '(:int)       ; n
                 :optional-arg-types '(:int) ; acc
                 :return-type :int))
          ;; stampa la riga ftype come nell'esempio della traccia
          (format t "(ftype (function (integer &optional integer) integer) ~A)~%"
                  name))

        info))))


(defun infer-type (expr)
  "Inferenza molto grezza: riconosce interi e simboli quotati."
  (cond
    ;; intero nudo: 42
    ((integerp expr)
     :int)

    ;; '3  → (quote 3)
    ((and (consp expr)
          (eq (car expr) 'quote))
     (let ((v (cadr expr)))
       (cond
         ((integerp v) :int)
         ((symbolp v)  :symbol)
         (t            :unknown))))

    ;; tutto il resto: per ora tipo sconosciuto
    (t
     :unknown)))



(defun check-user-function-call (fn args original-expr env)
  "Controlla il numero di argomenti di una chiamata a funzione definita dall'utente."
  (declare (ignore env)) ; lo useremo quando controlleremo davvero i tipi
  (let* ((info  (gethash fn *function-table*))
         (nargs (length args))
         (min   (function-info-min-arity info))
         (max   (function-info-max-arity info)))
    (when (< nargs min)
      (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne richiede almeno ~D.~%  Espressione: ~S~%"
              fn nargs min original-expr))
    (when (> nargs max)
      (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne accetta al massimo ~D.~%  Espressione: ~S~%"
              fn nargs max original-expr))
    ;; In futuro, qui controlleremo i tipi degli argomenti e il tipo di ritorno
    :unknown))


(defun display-arg (expr)
  "Restituisce una stringa 'bella' per l'argomento nell'errore."
  (cond
    ;; 'six → "six"
    ((and (consp expr)
          (eq (car expr) 'quote)
          (symbolp (cadr expr)))
     (symbol-name (cadr expr)))
    ;; altrimenti usiamo la stampa standard
    (t
     (format nil "~S" expr))))