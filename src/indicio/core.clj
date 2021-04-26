(ns indicio.core
  (:require
   [clojure.string :as str]
   [tla-edn.core :as tla-edn])
  (:import
   (tlc2.output IMessagePrinterRecorder MP EC)
   (util UniqueString)))

(defn- private-field
  ([obj fn-name-string]
   (let [m (.. obj getClass (getDeclaredField fn-name-string))]
     (. m (setAccessible true))
     (. m (get obj))))
  ([obj super-klass fn-name-string]
   (let [m (.. super-klass (getDeclaredField fn-name-string))]
     (. m (setAccessible true))
     (. m (get obj)))))

(defn tlc-result-handler
  [tlc-runner]
  (let [recorder-atom (atom {:others []})
        record #(swap! recorder-atom merge %)
        recorder (reify IMessagePrinterRecorder
                   (record [_ code objects]
                     (condp = code
                       EC/TLC_INVARIANT_VIOLATED_BEHAVIOR
                       (record {:violation {:type :invariant
                                            :name (first objects)}})

                       EC/TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE
                       (record {:error-messages (str/split (last objects) #"\n")})

                       EC/TLC_INVARIANT_VIOLATED_INITIAL
                       (record {:violation {:type :invariant
                                            :name (first objects)
                                            :initial-state? true}})

                       EC/TLC_DEADLOCK_REACHED
                       (record {:violation {:type :deadlock}})

                       (swap! recorder-atom update :others conj
                              [code objects]))))]
    (try
      (let [tlc-result (do (MP/setRecorder recorder)
                           (tlc-runner))
            recorder-info @recorder-atom
            _ (def recorder-info recorder-info)
            {:keys [:result
                    :info]} (if-some [error-trace (-> (private-field tlc-result "recorder")
                                                      .getMCErrorTrace
                                                      (.orElse nil))]
                              (let [states (->> (.getStates error-trace)
                                                (mapv bean))
                                    stuttering-state (some #(when (:stuttering %) %) states)
                                    back-to-state (some #(when (:backToState %) %) states)]
                                {:result (->> states
                                              ;; We don't want to return the state which
                                              ;; is stuttering, it's always equals to the
                                              ;; anterior.
                                              (remove :stuttering)
                                              (mapv (fn [state]
                                                      (->> state
                                                           :variables
                                                           (some #(when (= (.getName %) "main_var")
                                                                    (.getTLCValue %))))))
                                              (mapv tla-edn/to-edn)
                                              (map-indexed (fn [idx v] [idx v]))
                                              (into []))
                                 :info (merge (dissoc recorder-info :others)
                                              (cond
                                                stuttering-state
                                                {:violation {:type :stuttering
                                                             :state-number (:stateNumber stuttering-state)}}

                                                back-to-state
                                                {:violation {:type :back-to-state}}))})
                              (let [initial-state (when (-> recorder-info :violation :initial-state?)
                                                    ;; If we have a initial state violation, `MCError` is `nil`,
                                                    ;; but the state is stored in the main checker.
                                                    (-> (private-field tlc2.TLCGlobals/mainChecker
                                                                       tlc2.tool.AbstractChecker
                                                                       "errState")
                                                        bean
                                                        :vals
                                                        (.get (UniqueString/uniqueStringOf "main_var"))
                                                        tla-edn/to-edn))]
                                (cond
                                  initial-state {:result [[0 initial-state]]
                                                 :info (dissoc recorder-info :others)}

                                  :else
                                  {:result :ok})))]
        {:result (if (some-> tlc2.TLCGlobals/mainChecker .theFPSet .size)
                   result
                   :error)
         :result-info (if (-> info :violation :name (= ::show-example-invariant))
                        ;; If the user didn't ask for some check (through an
                        ;; invariant or a temporal property) and there was some
                        ;; violation (which in reality is just a example of a trace
                        ;; which satisfies the spec), then we get here.
                        (-> info
                            (dissoc :violation)
                            (assoc :trace-example {}))
                        info)
         :distinct-states (some-> tlc2.TLCGlobals/mainChecker .theFPSet .size)
         :generated-states (some-> tlc2.TLCGlobals/mainChecker .getStatesGenerated)})
      (catch Exception ex
        {:result :error
         :result-info (.getMessage ex)
         :distinct-states (some-> tlc2.TLCGlobals/mainChecker .theFPSet .size)
         :generated-states (some-> tlc2.TLCGlobals/mainChecker .getStatesGenerated)})
      (finally
        (MP/unsubscribeRecorder recorder)))))
