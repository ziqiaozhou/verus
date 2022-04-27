mod pervasive;

mod library {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::map::*,
    };

    #[spec]
    pub fn full_imap<K,V>(im:Map<K,V>) -> bool {
        forall(|k| im.dom().contains(k))
    }
}

// TODO(help): what's the equivalent of a module here?
mod host_identifiers {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::pervasive::*,
        crate::pervasive::set::*
    };

    fndecl!(pub fn num_hosts() -> int);

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    // TODO: Chris is suspicious that this argumentless-forall mightn't work
    pub fn axiom_num_hosts() {
        ensures(num_hosts() > 0);
    }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item.
    // Sure would be nice to have it.
    //type HostId = int;
    #[derive(PartialEq, Eq, Structural)]
    pub struct HostId { pub value: int }

    #[spec]
    pub fn ValidHostId(h: HostId) -> bool {
        0 <= h.value && h.value < num_hosts()
    }

    #[spec]
    fn AllHosts() -> Set<HostId>
    {
        Set::new(|h: HostId| ValidHostId(h))
            //&& 0<=h.value<num_hosts()  // don't need Dafny's finite-set heuristic
    }
}

mod network {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
    };
    
    // NB jonh renamed to NetMessage to remedy ambiguity with protocol Message (payload).
    #[derive(PartialEq, Eq, Structural)]
    pub struct NetMessage<Payload> {
        pub sender: HostId,
        pub payload: Payload
    }

    // TODO(design): This is a lot of syntax for 'struct'; looking for brevity.
    //#[derive(PartialEq, Eq, Structural)]
    pub struct MessageOps<Payload>
    {
        pub recv:Option<NetMessage<Payload>>,
        pub send:Option<NetMessage<Payload>>,
        pub signed_msgs_to_check:Set<NetMessage<Payload>>
    }

    impl<Payload> MessageOps<Payload> {
        #[spec]
        pub fn is_send(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_Some()
        }

        #[spec]
        pub fn is_recv(self) -> bool {
               true
            && self.recv.is_Some()
            && self.send.is_None()
        }

        #[spec]
        pub fn no_send_recv(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_None()
        }
    }

    //#[derive(PartialEq, Eq, Structural)]
    // Too bad, Set can't be Structural, so you'll have to .equal().
    pub struct Variables<Payload> {
        pub sent_msgs: Set<NetMessage<Payload>>
    }

    impl<Payload> Variables<Payload> {
        #[spec]
        pub fn init(self: Variables<Payload>) -> bool {
            equal(self.sent_msgs, set![])
        }

        #[spec]
        pub fn next(v: Variables<Payload>, vp: Variables<Payload>, msg_ops: MessageOps<Payload>, sender: HostId) -> bool {
               true
            // Only allow receipt of a message if we've seen it has been sent.
            && (msg_ops.recv.is_Some() >>= v.sent_msgs.contains(msg_ops.recv.value()))
            // Record the sent message, if there was one.
            && equal(vp.sent_msgs,
                    v.sent_msgs.union(
                        if msg_ops.send.is_Some() && msg_ops.send.value().sender == sender {
                            set![msg_ops.send.value()]
                        } else {
                            set![]
                        }))
            && msg_ops.signed_msgs_to_check.subset_of(v.sent_msgs)
        }
    }
}

mod messages {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::map::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::network::*,
    };

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type SequenceID = nat;
    #[derive(PartialEq, Eq, Structural)]
    pub struct SequenceID  { pub value: nat }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type ViewNum = nat
    #[derive(PartialEq, Eq, Structural)]
    pub struct ViewNum  { pub value: nat }

    pub struct ClientOperation {
        pub sender: HostId,
        pub timestamp: nat
    }

    pub enum OperationWrapper {
        Noop,
        ClientOp { clientOperation: ClientOperation }
    }

    #[spec]
    pub fn senders_of(msgs: Set<NetMessage<Message>>) -> Set<HostId> {
        msgs.map(|msg: NetMessage<Message>| msg.sender)
    }

    #[spec]
    pub fn unique_senders(msgs: Set<NetMessage<Message>>) -> bool {
        forall(|m1, m2| #[auto_trigger]
                     true
                  && msgs.contains(m1)
                  && msgs.contains(m2)
                  && !equal(m1, m2)
              >>= m1.sender != m2.sender)
    }

    pub struct PreparedCertificate {
        pub votes: Set<NetMessage<Message>>
    }

    impl PreparedCertificate {
        #[spec]
        pub fn prototype(self) -> Message {
            recommends(self.votes.len() > 0);
            choose(|prot| self.votes.contains(prot)).payload
        }

        #[spec]
        pub fn wf(self) -> bool {
            forall(|v| #[auto_trigger] self.votes.contains(v) >>= v.payload.is_Prepare())
        }

        #[spec]
        pub fn empty(self) -> bool {
            self.votes.len() == 0
        }

        #[spec]
        pub fn valid(self, quorum_size: nat) -> bool {
               false
            || self.empty()
            || (   true
                && self.votes.len() == quorum_size
                && self.wf()
                // messages have to be votes that match eachother by the prototype 
                && forall(|v| #[auto_trigger] self.votes.contains(v) >>= equal(v.payload, self.prototype()))
                && unique_senders(self.votes)
                )
        }
    }

    pub struct ViewChangeMsgsSelectedByPrimary {
        pub msgs: Set<NetMessage<Message>>
    }

    impl ViewChangeMsgsSelectedByPrimary {
        #[spec]
        pub fn valid(self, view: ViewNum, quorum_size: nat) -> bool {
               true
            && self.msgs.len() > 0
            // All the ViewChange messages have to be for the same View. 
            && forall(|v| #[auto_trigger] self.msgs.contains(v) >>=
                         true
                      && v.payload.is_ViewChangeMsg()
                      && v.payload.wf()
                      && v.payload.get_new_view() == view
                      )
            && unique_senders(self.msgs)
            && self.msgs.len() == quorum_size
        }
    }

    #[is_variant]
    pub enum Message {
        PrePrepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Prepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Commit { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        ClientRequest { client_op: ClientOperation },
        ViewChangeMsg { new_view: ViewNum, certificates: Map<SequenceID, PreparedCertificate> },
        NewViewMsg { new_view: ViewNum, vc_msgs: ViewChangeMsgsSelectedByPrimary },
    }

    impl Message {
        // TODO(utaal): is_ generators are essential. But field accessors are also
        // essential; observe this heaping mound of tedious, error-prone boilerplate:
        #[spec] pub fn get_new_view(self) -> ViewNum {
            recommends(self.is_ViewChangeMsg() || self.is_NewViewMsg());
            match self {
                Message::ViewChangeMsg { new_view, .. } => new_view,
                Message::NewViewMsg { new_view, .. } => new_view,
                _ => arbitrary()
            }
        }
        #[spec] pub fn get_view(self) -> ViewNum {
            recommends(self.is_PrePrepare() || self.is_Prepare() || self.is_Commit());
            match self {
                Message::PrePrepare { view, .. } => view,
                Message::Prepare { view, .. } => view,
                Message::Commit { view, .. } => view,
                _ => arbitrary(),
            }
        }
        #[spec] pub fn get_seq_id(self) -> SequenceID {
            recommends(self.is_PrePrepare() || self.is_Prepare() || self.is_Commit());
            match self {
                Message::PrePrepare { seq_id, .. } => seq_id,
                Message::Prepare { seq_id, .. } => seq_id,
                Message::Commit { seq_id, .. } => seq_id,
                _ => arbitrary(),
            }
        }
        #[spec] pub fn get_operation_wrapper(self) -> OperationWrapper {
            recommends(self.is_PrePrepare() || self.is_Prepare() || self.is_Commit());
            match self {
                Message::PrePrepare { operation_wrapper, .. } => operation_wrapper,
                Message::Prepare { operation_wrapper, .. } => operation_wrapper,
                Message::Commit { operation_wrapper, .. } => operation_wrapper,
                _ => arbitrary(),
            }
        }
        #[spec] pub fn get_certificates(self) -> Map<SequenceID, PreparedCertificate> {
            recommends(self.is_ViewChangeMsg());
            match self {
                Message::ViewChangeMsg { certificates: certificates, .. } => certificates,
                _ => arbitrary(),
            }
        }
        #[spec] pub fn get_vc_msgs(self) -> ViewChangeMsgsSelectedByPrimary {
            recommends(self.is_NewViewMsg());
            match self {
                Message::NewViewMsg { vc_msgs: vc_msgs, .. } => vc_msgs,
                _ => arbitrary(),
            }
        }
        // ....end tedious boilerplate.

        #[spec]
        pub fn wf(self) -> bool {
            // TODO(jonh): Ewww
            // self.is_ViewChangeMsg() >>= full_imap(self.certificates())
            match self {
                Message::ViewChangeMsg { certificates, .. } => full_imap(certificates),
                _ => true,
            }
        }
    }
}

mod cluster_config {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        max_byzantine_faulty_replicas: nat,
        num_clients: nat
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.max_byzantine_faulty_replicas > 0 // Require non-trivial BFT system
            && self.num_clients > 0
        }

        #[spec]
        pub fn f(self) -> nat {
            recommends(self.wf());
            self.max_byzantine_faulty_replicas 
        }

        #[spec]
        pub fn n(self) -> nat {
            recommends(self.wf());
            3 * self.f() + 1
        }

        #[spec]
        pub fn cluster_size(self) -> nat {
            recommends(self.wf());
            self.n() + self.num_clients
        }

        #[spec]
        pub fn byzantine_safe_quorum(self) -> nat {
            recommends(self.wf());
            3 * self.f() + 1
        }

        #[spec]
        pub fn agreement_quorum(self) -> nat {
            recommends(self.wf());
            2 * self.f() + 1
        }

        #[spec]
        pub fn is_honest_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && self.f() <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_faulty_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.f()
        }

        #[spec]
        pub fn is_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_client(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && self.n() <= id.value
            && id.value < num_hosts()
        }
    }
}

mod client {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        pub my_id: HostId,
        pub cluster_config: cluster_config::Constants
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.is_client(self.my_id)    // NB: jonh upgraded to symbolic name
        }

        #[spec]
        pub fn configure(self, id: HostId, cluster_config: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_config
        }
    }

    // Placeholder for possible client state
    #[derive(PartialEq, Eq, Structural)]
    pub struct Variables {
        last_request_timestamp: nat,
        last_reply_timestamp: nat
    }

    impl Variables {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && self.last_request_timestamp >= self.last_reply_timestamp
        }
    }
    
    #[spec]
    pub fn pending_requests(c: Constants, v: Variables) -> nat {
        recommends(v.wf(c));
        v.last_request_timestamp - v.last_reply_timestamp
    }

    #[spec]
    pub fn send_client_operation(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        let msg = msg_ops.send.value();
           true
        && v.wf(c)
        && msg_ops.is_send()
        && pending_requests(c, v) == 0
        && msg.payload.is_ClientRequest()
        && msg.sender == c.my_id
        && msg.payload.get_ClientRequest_client_op().sender == c.my_id
        && msg.payload.get_ClientRequest_client_op().timestamp == v.last_request_timestamp + 1
        && vp == Variables {
            last_request_timestamp: v.last_request_timestamp + 1,
            ..vp }
        // ...
    }
    
    #[spec]
    pub fn init(c: Constants, v: Variables) -> bool {
           true
        && v.wf(c)
        && v.last_request_timestamp == 0
        && v.last_reply_timestamp == 0
    }

    pub enum Step {
        SendClientOperationStep()
    }

    #[spec]
    pub fn next_step(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>, step: Step) -> bool {
        match step {
            Step::SendClientOperationStep() => send_client_operation(c, v, vp, msg_ops)
        }
    }

    #[spec]
    pub fn next(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        exists(|step| next_step(c, v, vp, msg_ops, step))
    }
}

mod replica {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
        crate::pervasive::map::*,
    };

    pub struct Constants {
        pub my_id: HostId,
        pub cluster_config: cluster_config::Constants
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.is_replica(self.my_id)
        }

        #[spec] pub fn configure(self, id: HostId, cluster_conf: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_conf
        }
    }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type PrepareProofSet = Map<HostId, NetMessage<Message>>
    // TODO(utaal): Maps can't Structural, either.
    //#[derive(PartialEq, Eq, Structural)]
    pub struct PrepareProofSet {
        pub map: Map<HostId, network::NetMessage<Message>>
    }

    impl PrepareProofSet {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
            // TODO(utual): index(x) ==> [x]
            forall(|x| #[auto_trigger]
                   true
                && self.map.contains(x)
                && c.cluster_config.is_replica(self.map.index(x).sender))
        }

        #[spec]
        pub fn len(self) -> nat {
            self.map.dom().len()
        }
    }

    //type PrepareProofSet = Map<HostId, NetMessage<Message>>
    // TODO(utaal): Maps can't Structural, either.
    //#[derive(PartialEq, Eq, Structural)]
    pub struct CommitProofSet {
        map: Map<HostId, network::NetMessage<Message>>
    }

    impl CommitProofSet {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
            // TODO(utual): index(x) ==> [x]
            forall(|x| #[auto_trigger]
                   true
                && self.map.contains(x)
                && c.cluster_config.is_replica(self.map.index(x).sender))
        }

        #[spec]
        pub fn len(self) -> nat {
            self.map.dom().len()
        }
    }

    //type PrePreparesRecvd = Map<SequenceID, Option<network::NetMessage<Message>>>
    // TODO(utaal): Maps can't Structural, either.
    pub struct PrePreparesRcvd {
        pub map: Map<SequenceID, Option<network::NetMessage<Message>>>
    }

    impl PrePreparesRcvd {
        #[spec] pub fn wf(self) -> bool {
               true
            && full_imap(self.map)
            && forall(|x| #[auto_trigger]
                      self.map.contains(x) && self.map.index(x).is_Some()
                      >>= self.map.index(x).value().payload.is_PrePrepare())
        }
    }

    // TODO(utaal): discuss: I'm pub-ifying a lot of structs because my proof module
    // wants to reach into them. I wonder what the right software-engineering-clean
    // pattern should be. Like, I'd still like to tell other modules to keep their
    // mitts off these fields, but maybe the proof module wants to be a "friend" sort
    // of thing?
    pub struct WorkingWindow {
        pub committed_client_operations: Map<SequenceID, Option<OperationWrapper>>,
        pub pre_prepares_rcvd: PrePreparesRcvd,
        pub prepares_rcvd: Map<SequenceID, PrepareProofSet>,
        pub commits_rcvd: Map<SequenceID, CommitProofSet>,
    }

    // TODO(chris): Discussion: I'm needing auto_trigger on EVERY forall. Is that expected?
    // Is it a sign that I'm an idiot? Will this be why this proof is so timeout-prone?
    impl WorkingWindow {
        #[spec] pub fn wf(self, c: Constants) -> bool {
               true
            && full_imap(self.committed_client_operations)
            && full_imap(self.prepares_rcvd)
            && full_imap(self.commits_rcvd)
            && self.pre_prepares_rcvd.wf()
            && forall(|seqID| #[auto_trigger] self.prepares_rcvd.contains(seqID) >>= self.prepares_rcvd.index(seqID).wf(c))
            && forall(|seqID| #[auto_trigger] self.commits_rcvd.contains(seqID) >>= self.commits_rcvd.index(seqID).wf(c))
        }
    }

    pub struct ViewChangeMsgs { msgs: Set<network::NetMessage<Message>> }
    impl ViewChangeMsgs {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && forall(|msg| #[auto_trigger] self.msgs.contains(msg) >>=
                     true
                  && msg.payload.is_ViewChangeMsg()
                  && c.cluster_config.is_replica(msg.sender))
        }
    }

    pub struct NewViewMsgs { msgs: Set<network::NetMessage<Message>> }
    impl NewViewMsgs {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && forall(|msg| #[auto_trigger] self.msgs.contains(msg) >>=
                     true
                  && msg.payload.is_NewViewMsg()
                  && c.cluster_config.is_replica(msg.sender))
        }
    }

    pub struct Variables {
        pub view: ViewNum,
        pub working_window: WorkingWindow,
        pub view_change_msgs_recvd: ViewChangeMsgs,
        pub new_view_msgs_recvd: NewViewMsgs,
    }
    impl Variables {
        #[spec] pub fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && self.working_window.wf(c)
            && self.view_change_msgs_recvd.wf(c)
            && self.new_view_msgs_recvd.wf(c)
        }
    }

    #[spec] fn primary_for_view(c: Constants, view: ViewNum) -> HostId {
        HostId{ value: (view.value % c.cluster_config.n()) as int }
    }

    #[spec] fn current_primary(c: Constants, v: Variables) -> HostId {
        recommends(v.wf(c));
        primary_for_view(c, v.view)
    }

    // TODO(jonh): this was opaque in Dafny. Superstition?
    #[spec] fn have_sufficient_vc_msgs_to_move_to(c: Constants, v: Variables, new_view: ViewNum) -> bool {
        recommends(v.wf(c));
        let relevant_vc_msgs =
            Set::new(|vc_msg|
                   true
                && v.view_change_msgs_recvd.msgs.contains(vc_msg)
                && vc_msg.payload.get_new_view().value >= new_view.value);
        let senders = senders_of(relevant_vc_msgs);
        senders.len() >= c.cluster_config.byzantine_safe_quorum() //F+1
    }

    // TODO(jonh): this was opaque in Dafny. Superstition?
    #[spec] fn has_collected_proof_my_view_is_agreed(c: Constants, v: Variables) -> bool {
        let vc_msgs_for_my_view = Set::new(| msg|
                                           true
                                       && v.view_change_msgs_recvd.msgs.contains(msg)
                                       && msg.payload.get_new_view() == v.view
                                       );
        let senders = senders_of(vc_msgs_for_my_view);
           true
        && v.wf(c)
        && (
               false
            || v.view.value == 0 // View 0 is active initially therefore it is initially agreed.
            || senders.len() >= c.cluster_config.agreement_quorum()
           )
    }

    #[proof] #[verifier(decreases_by)]
    fn highest_view_prepare_certificate_decreases(prepare_certificates: Set<PreparedCertificate>)
    {
        requires([
                 prepare_certificates.finite(),
                 0 < prepare_certificates.len()
        ]);
        assert(!equal(prepare_certificates, set![]));
        let any = choose(|any| prepare_certificates.contains(any));
        assert(equal(any, prepare_certificates.choose()));
        assert(prepare_certificates.contains(any));
        let small = prepare_certificates.difference(set![any]);
        let reconstructed = small.insert(any);
        assert_forall_by(|e| {
            ensures(reconstructed.contains(e) == prepare_certificates.contains(e));
            if equal(e, any) {
                assert(reconstructed.contains(e));
                assert(prepare_certificates.contains(e));
                assert(reconstructed.contains(e) == prepare_certificates.contains(e));
            } else {
                assert(reconstructed.contains(e) == prepare_certificates.contains(e));
            }
        });
        assert(reconstructed.ext_equal(prepare_certificates));
        assert(equal(reconstructed, prepare_certificates));
        assert(small.len() + 1 == prepare_certificates.len());
        assert(small.len() < prepare_certificates.len());
    }

    // Constructively demonstrate that we can compute the certificate with the highest View.
    #[spec] fn highest_view_prepare_certificate(prepare_certificates: Set<PreparedCertificate>) -> PreparedCertificate {
        // TODO(chris): "only one call to recommends allowed"? Aw c'mooooon.
        // TODO(jonh): add decreases_when?
        recommends([
           forall(|cert| #[auto_trigger] prepare_certificates.contains(cert) >>= cert.wf() && !cert.empty()),
            prepare_certificates.len() > 0
        ]);
        // TODO(chris): "only one call to ensures allowed"? Aw c'mooooon.
        // TODO(jonh): guess this is a lemma
//        ensures(|out| [
//            prepare_certificates.contains(out),
//        // TODO(chris): Eeww. Having to type the out param is a bummer. Maybe macroland solves
//        // this?
//            forall(|other| prepare_certificates.contains(other) >>=
//                out.prototype().get_view().value >= other.prototype().get_view().value)
//        ]);
        decreases(prepare_certificates.len());
        decreases_by(highest_view_prepare_certificate_decreases);

        let any = choose(|any| prepare_certificates.contains(any));
        if prepare_certificates.len() == 0 {
            any // silly
        } else if prepare_certificates.len() == 1 {
            // Nothing to prove in a fn; maybe needed in a lemma?
            // Library.SingletonSetAxiom(any, prepare_certificates);
            any
        } else {
            let rest = prepare_certificates.difference(set![any]);
            let highest_of_rest = highest_view_prepare_certificate(rest);
            if any.prototype().get_view().value > highest_of_rest.prototype().get_view().value {
                any
            } else {
                highest_of_rest
            }
        }
    }

    #[spec] fn calculate_restriction_for_seq_id(c: Constants, v: Variables, seq_id: SequenceID, new_view_msg: network::NetMessage<Message>) -> Option<OperationWrapper>
    {
        recommends([
            v.wf(c),
            new_view_msg.payload.is_NewViewMsg(),
            new_view_msg.payload.get_vc_msgs().valid(v.view, c.cluster_config.agreement_quorum()),
            new_view_msg.payload.get_new_view() == v.view,
            new_view_msg.sender == current_primary(c, v),
        ]);

        // 1. Take the NewViewMsg for the current View.
        // 2. Go through all the ViewChangeMsg-s in the NewView and take the valid full 
        //    PreparedCertificates from them for the seqID.
        // 3. From all the collected PreparedCertificates take the one with the highest View.
        // 4. If it is empty  we need to fill with NoOp.
        // 5. If it contains valid full quorum we take the Client Operation and insist it will be committed in the new View.
        // var preparedCertificates := set cert | 

        let relevant_prepare_certificates = new_view_msg.payload.get_vc_msgs().msgs
            .map(|vcm| vcm.payload.get_certificates().index(seq_id))
            .filter(|cert| cert.wf() && !cert.empty());

        if relevant_prepare_certificates.len() == 0 {
            // TODO(utaal): Why does Rust try for std::option::Option, even though I explicitly
            // use crate::pervasive::*?
            pervasive::option::Option::Some(OperationWrapper::Noop)
        } else {
          let highest_view_cert = highest_view_prepare_certificate(relevant_prepare_certificates);
          pervasive::option::Option::Some(highest_view_cert.prototype().get_operation_wrapper())
        }
    }

    #[spec] fn view_is_active(c: Constants, v: Variables) -> bool {
        let relevant_new_view_msgs = v.new_view_msgs_recvd.msgs.filter(|msg| msg.payload.get_new_view() == v.view);
           true
        && v.wf(c)
        && (
               false
            || v.view.value == 0 // View 0 is active initially. There are no View Change messages for it.
            || relevant_new_view_msgs.len() == 1 // The NewViewMsg that the Primary sends contains in itself the selected Quorum of
                                        // ViewChangeMsg-s based on which we are going to rebuild the previous View's working window.
        )
    }

    // Predicate that describes what is needed and how we mutate the state v into v' when SendPrePrepare
    // Action is taken. We use the "binding" variable msgOps through which we send/recv messages.
    #[spec] fn send_pre_prepare(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>) -> bool
    {
        // TODO(utaal): it often makes more sense to 'let' things in the middle of the story
        // but presently verus demands we pull it to the front.
        let msg = msg_ops.send.value();
           true
        && v.wf(c)
        && msg_ops.is_send()
        && current_primary(c, v) == c.my_id
        && msg.payload.is_PrePrepare() // We have a liveness bug here, we need some state that says for the client which operation ID-s we have executed
        && equal(v, vp)
    }

    // Node local invariants that we need to satisfy dafny requires. This gets proven as part of the Distributed system invariants.
    // That is why it can appear as enabling condition, but does not need to be translated to runtime checks to C++.
    // For this to be safe it has to appear in the main invarinat in the proof.
    // NB: Verus fns never require! Just recommend. So that's new.
    #[spec] fn lite_inv(c:Constants, v:Variables) -> bool {
           true
        && v.wf(c)
        && forall(|new_view_msg| #[auto_trigger]
            v.new_view_msgs_recvd.msgs.contains(new_view_msg) >>=
                   true
                && new_view_msg.payload.get_vc_msgs().valid(v.view, c.cluster_config.agreement_quorum())
                && primary_for_view(c, new_view_msg.payload.get_new_view()) == new_view_msg.sender)
    }

    // For clarity here we have extracted all preconditions that must hold for a Replica to accept a PrePrepare
    // NB(jonh): {:opaque}
    #[spec] fn is_valid_pre_prepare_to_accept(c:Constants, v:Variables, msg:network::NetMessage<Message>) -> bool
    {
        recommends(lite_inv(c, v));
        // TODO(utaal): (repeated) unhappy to pull up lets
        let new_view_msgs = v.new_view_msgs_recvd.msgs.filter(|msg| msg.payload.get_new_view() == v.view);
        let new_view_msg = new_view_msgs.choose();

           true
        && v.wf(c)
        && lite_inv(c, v)
        && msg.payload.is_PrePrepare()
        && c.cluster_config.is_replica(msg.sender)
        && view_is_active(c, v)
        && msg.payload.get_view() == v.view
        && msg.sender == current_primary(c, v)
        && v.working_window.pre_prepares_rcvd.map.index(msg.payload.get_seq_id()).is_None()
        && if new_view_msgs.len() == 0 {
                true
            } else {
                   true
                && new_view_msgs.len() == 1
                && equal(pervasive::option::Option::Some(msg.payload.get_operation_wrapper()),
                       calculate_restriction_for_seq_id(c, v, msg.payload.get_seq_id(), new_view_msg))
            }

    }

    // Predicate that describes what is needed and how we mutate the state v into v' when RecvPrePrepare
    // Action is taken. We use the "binding" variable msg_ops through which we send/recv messages. In this 
    // predicate we need to reflect in our next state that we have received the PrePrepare message.
    #[spec] fn recv_pre_prepare(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>) -> bool
    {
        let msg = msg_ops.recv.value();
           true
        && v.wf(c)
        && msg_ops.is_recv()
        && is_valid_pre_prepare_to_accept(c, v, msg)
        && equal(vp, Variables {
            working_window: WorkingWindow {
                pre_prepares_rcvd: PrePreparesRcvd {
                    map: v.working_window.pre_prepares_rcvd.map.insert(
                                 msg.payload.get_seq_id(), pervasive::option::Option::Some(msg))
                },
                ..v.working_window },
            ..v })
    }

    // For clarity here we have extracted all preconditions that must hold for a Replica to accept a Prepare
    #[spec] fn is_valid_prepare_to_accept(c:Constants, v:Variables, msg:network::NetMessage<Message>) -> bool
    {
           true
        && v.wf(c)
        && msg.payload.is_Prepare()
        && c.cluster_config.is_replica(msg.sender)
        && view_is_active(c, v)
        && msg.payload.get_view() == v.view
        && v.working_window.pre_prepares_rcvd.map.index(msg.payload.get_seq_id()).is_Some()
        && equal(v.working_window.pre_prepares_rcvd.map.index(msg.payload.get_seq_id()).value().payload.get_operation_wrapper(), msg.payload.get_operation_wrapper())
        && !v.working_window.prepares_rcvd.index(msg.payload.get_seq_id()).map.contains(msg.sender) // We stick to the first vote from a peer.
    }

    // Predicate that describes what is needed and how we mutate the state v into v' when RecvPrepare
    // Action is taken. We use the "binding" variable msg_ops through which we send/recv messages. In this 
    // predicate we need to reflect in our next state that we have received the Prepare message.
    #[spec] fn recv_prepare(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>) -> bool
    {
        let msg = msg_ops.recv.value();
           true
        && v.wf(c)
        && msg_ops.is_recv()
        && is_valid_prepare_to_accept(c, v, msg)
        && equal(vp, Variables {
            working_window: WorkingWindow {
                prepares_rcvd: v.working_window.prepares_rcvd.insert(
                             msg.payload.get_seq_id(),
                             PrepareProofSet {
                                 map: v.working_window.prepares_rcvd.index(msg.payload.get_seq_id()).map.insert(
                                 msg.sender, msg) }),
                ..v.working_window },
            ..v })
    }
    
    #[spec] fn is_valid_commit_to_accept(c:Constants, v:Variables, msg:network::NetMessage<Message>) -> bool
    {
           true
        && v.wf(c)
        && msg.payload.is_Commit()
        && c.cluster_config.is_replica(msg.sender)
        && view_is_active(c, v)
        && msg.payload.get_view() == v.view
        && v.working_window.pre_prepares_rcvd.map.index(msg.payload.get_seq_id()).is_Some()
        && equal(v.working_window.pre_prepares_rcvd.map.index(msg.payload.get_seq_id()).value().payload.get_operation_wrapper(),
            msg.payload.get_operation_wrapper())
        && !v.working_window.commits_rcvd.index(msg.payload.get_seq_id()).map.contains(msg.sender) // We stick to the first vote from a peer.
    }

    #[spec] fn recv_commit(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>) -> bool
    {
        let msg = msg_ops.recv.value();
           true
        && v.wf(c)
        && msg_ops.is_recv()
        && is_valid_commit_to_accept(c, v, msg)
        && equal(vp, Variables {
            working_window: WorkingWindow {
                commits_rcvd: v.working_window.commits_rcvd.insert(
                    msg.payload.get_seq_id(),
                    CommitProofSet {
                        map: v.working_window.commits_rcvd.index(msg.payload.get_seq_id()).map.insert(msg.sender, msg) }),
                ..v.working_window
            },
            ..v
        })
    }

    #[spec] fn quorum_of_prepares(c:Constants, v:Variables, seqID:SequenceID) -> bool {
           true
        && v.wf(c)
        && v.working_window.prepares_rcvd.index(seqID).len() >= c.cluster_config.agreement_quorum()
    }

    #[spec] fn quorum_of_commits(c:Constants, v:Variables, seqID:SequenceID) -> bool {
           true
        && v.wf(c)
        && v.working_window.commits_rcvd.index(seqID).len() >= c.cluster_config.agreement_quorum()
    }

    #[spec] fn DoCommit(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>, seqID:SequenceID) -> bool
    {
        let msg = v.working_window.pre_prepares_rcvd.map.index(seqID).value();
           true
        && v.wf(c)
        && msg_ops.no_send_recv()
        && quorum_of_prepares(c, v, seqID)
        && quorum_of_commits(c, v, seqID)
        && v.working_window.pre_prepares_rcvd.map.index(seqID).is_Some()
        // TODO: We should be able to commit empty (Noop) operations as well
        && equal(vp, Variables {
            working_window: WorkingWindow {
                committed_client_operations: v.working_window.committed_client_operations.insert(
        // TODO(utaal): Why is default Some in scope?
                     msg.payload.get_seq_id(), pervasive::option::Option::Some(msg.payload.get_operation_wrapper())),
                ..v.working_window
            },
          ..v })
    }

    // Predicate that describes what is needed and how we mutate the state v into v' when SendPrepare
    // Action is taken. We use the "binding" variable msg_ops through which we send/recv messages. In this 
    // predicate we do not mutate the next state, relying on the fact that messages will be broadcast
    // and we will be able to receive our own message and store it as described in the RecvPrepare predicate.
    #[spec]
    fn send_prepare(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>, seq_id:SequenceID) -> bool
    {
           true
        && v.wf(c)
        && msg_ops.is_send()
        && view_is_active(c, v)
        && v.working_window.pre_prepares_rcvd.map.index(seq_id).is_Some()
        && equal(msg_ops.send, pervasive::option::Option::Some(network::NetMessage {
            sender: c.my_id,
            payload: Message::Prepare {
                view: v.view,
                seq_id: seq_id,
                operation_wrapper: v.working_window.pre_prepares_rcvd.map.index(seq_id).value().payload.get_operation_wrapper()
            }}))
//        && assert msg_ops.send.value.payload.Prepare?; true
        && equal(vp, v)
    }

    // Predicate that describes what is needed and how we mutate the state v into vp when SendCommit
    // Action is taken. We use the "binding" variable msg_ops through which we send/recv messages. In this 
    // predicate we do not mutate the next state, relying on the fact that messages will be broadcast
    // and we will be able to receive our own message and store it as described in the RecvCommit predicate.
    #[spec]
    fn send_commit(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>, seq_id:SequenceID) -> bool
    {
           true
        && v.wf(c)
        && msg_ops.is_send()
        && view_is_active(c, v)
        && quorum_of_prepares(c, v, seq_id)
        && v.working_window.pre_prepares_rcvd.map.index(seq_id).is_Some()
        && equal(msg_ops.send, pervasive::option::Option::Some(network::NetMessage{
            sender: c.my_id,
            payload: Message::Commit{
                view: v.view,
                seq_id: seq_id,
                operation_wrapper: v.working_window.pre_prepares_rcvd.map.index(seq_id).value().payload.get_operation_wrapper()
        }}))
//        && assert msg_ops.send.value.payload.Commit?; true

        && equal(vp, v)
    }

    /* LEFT OFF at: LeaveView */

    // TODO(jonh): add map.contains that means don().contains()
    #[spec] pub fn init(c:Constants, v:Variables) -> bool {
           true
        && v.view.value == 0
        && forall(|seq_id| #[auto_trigger] v.working_window.committed_client_operations.dom().contains(seq_id)
                >>= v.working_window.committed_client_operations.index(seq_id).is_None())
        && forall(|seq_id| #[auto_trigger] v.working_window.pre_prepares_rcvd.map.contains(seq_id)
                >>= v.working_window.pre_prepares_rcvd.map.index(seq_id).is_None())
        && forall(|seq_id| #[auto_trigger] v.working_window.prepares_rcvd.contains(seq_id)
                >>= equal(v.working_window.prepares_rcvd.index(seq_id).map, map![]))
        && forall(|seq_id| #[auto_trigger] v.working_window.commits_rcvd.contains(seq_id)
                >>= equal(v.working_window.commits_rcvd.index(seq_id).map, map![]))
        && equal(v.view_change_msgs_recvd.msgs, set![])
        && equal(v.new_view_msgs_recvd.msgs, set![])
    }

    pub enum Step {
        SendPrePrepareStep(),
        RecvPrePrepareStep(),
        SendPrepareStep { seq_id:SequenceID },
        RecvPrepareStep(),
        SendCommitStep { seq_id:SequenceID },
        RecvCommitStep(),
        DoCommitStep { seq_id:SequenceID }
    }

    #[spec] fn next_step(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>, step: Step) -> bool
    {
        match step {
            Step::SendPrePrepareStep() => send_pre_prepare(c, v, vp, msg_ops),
            Step::RecvPrePrepareStep() => recv_pre_prepare(c, v, vp, msg_ops),
            Step::SendPrepareStep { seq_id } => send_prepare(c, v, vp, msg_ops, seq_id),
            Step::RecvPrepareStep() => recv_prepare(c, v, vp, msg_ops),
            Step::SendCommitStep { seq_id } => send_commit(c, v, vp, msg_ops, seq_id),
            Step::RecvCommitStep() => recv_commit(c, v, vp, msg_ops),
            Step::DoCommitStep { seq_id } => false /* LEFT OFF */
        }
    }

    #[spec] fn next(c:Constants, v:Variables, vp:Variables, msg_ops:network::MessageOps<Message>) -> bool
    {
        exists(|step| next_step(c, v, vp, msg_ops, step))
    }
}

mod faulty_replica {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        pub my_id: HostId,
        pub cluster_config: cluster_config::Constants
    }
    impl Constants {
        #[spec] pub fn configure(self, id: HostId, cluster_conf: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_conf
        }
    }

    // Placeholder for possible client state
    #[derive(PartialEq, Eq, Structural)]
    pub struct Variables { }

    #[spec] fn arbitrary_behavior(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        true
    }

    pub enum Step {
        ArbitraryBehaviorStep()
    }

    #[spec]
    pub fn next_step(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>, step: Step) -> bool {
        match step {
            Step::ArbitraryBehaviorStep() => arbitrary_behavior(c, v, vp, msg_ops)
        }
    }

    #[spec]
    pub fn next(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        exists(|step| next_step(c, v, vp, msg_ops, step))
    }
    
}
    
mod distributed_system {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::seq::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    #[is_variant]
    pub enum HostConstants {
        Replica { replica_constants: replica::Constants },
        FaultyReplica { faulty_replica_constants: faulty_replica::Constants },
        Client { client_constants: client::Constants },
    }
    impl HostConstants {
        // TODO(utaal): soooo muuuuuch boooooilerplate
        #[spec] pub fn get_replica_constants(self) -> replica::Constants {
            recommends(self.is_Replica());
            match self {
                HostConstants::Replica { replica_constants, .. } => replica_constants,
                _ => arbitrary()
            }
        }
        #[spec] pub fn get_faulty_replica_constants(self) -> faulty_replica::Constants {
            recommends(self.is_FaultyReplica());
            match self {
                HostConstants::FaultyReplica { faulty_replica_constants, .. } => faulty_replica_constants,
                _ => arbitrary()
            }
        }
        #[spec] pub fn get_client_constants(self) -> client::Constants {
            recommends(self.is_Client());
            match self {
                HostConstants::Client { client_constants, .. } => client_constants,
                _ => arbitrary()
            }
        }
    }

    #[is_variant]
    pub enum HostVariables {
        Replica { replica_variables: replica::Variables },
        FaultyReplica { faulty_replica_variables: faulty_replica::Variables },
        Client { client_variables: client::Variables },
    }
    impl HostVariables {
        // TODO(utaal): soooo muuuuuch boooooilerplate
        #[spec] pub fn get_replica_variables(self) -> replica::Variables {
            recommends(self.is_Replica());
            match self {
                HostVariables::Replica { replica_variables, .. } => replica_variables,
                _ => arbitrary()
            }
        }
        #[spec] pub fn get_faulty_replica_variables(self) -> faulty_replica::Variables {
            recommends(self.is_FaultyReplica());
            match self {
                HostVariables::FaultyReplica { faulty_replica_variables, .. } => faulty_replica_variables,
                _ => arbitrary()
            }
        }
        #[spec] pub fn get_client_variables(self) -> client::Variables {
            recommends(self.is_FaultyReplica());
            match self {
                HostVariables::Client { client_variables, .. } => client_variables,
                _ => arbitrary()
            }
        }
    }

    pub struct Constants {
        pub hosts: Seq<HostConstants>,
        /* network: network::Constants, */
        pub cluster_config: cluster_config::Constants
    }
    impl Constants {
        #[spec] pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.cluster_size() == num_hosts()
            && self.hosts.len() == num_hosts()
            && forall(|id| #[auto_trigger] self.cluster_config.is_honest_replica(id) >>=
                   true
                && equal(self.hosts.index(id.value), HostConstants::Replica {
                    replica_constants: replica::Constants {
                        my_id: id,
                        cluster_config: self.cluster_config}})
                && self.hosts.index(id.value).get_replica_constants().configure(id, self.cluster_config)
                )
            && forall(|id| #[auto_trigger] self.cluster_config.is_faulty_replica(id) >>=
                   true
                && equal(self.hosts.index(id.value), HostConstants::FaultyReplica {
                    faulty_replica_constants: faulty_replica::Constants {
                        my_id: id,
                        cluster_config: self.cluster_config}})
                && self.hosts.index(id.value).get_faulty_replica_constants().configure(id, self.cluster_config)
                )
            && forall(|id| #[auto_trigger] self.cluster_config.is_client(id) >>=
                   true
                && equal(self.hosts.index(id.value), HostConstants::Client {
                    client_constants: client::Constants {
                        my_id: id,
                        cluster_config: self.cluster_config}})
                && self.hosts.index(id.value).get_client_constants().configure(id, self.cluster_config)
                )
        }
    }

    pub struct Variables {
        pub hosts: Seq<HostVariables>,
        pub network: network::Variables<Message>,
    }
    impl Variables {
        #[spec] pub fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && self.hosts.len() == c.hosts.len()
            && forall(|id| #[auto_trigger] c.cluster_config.is_honest_replica(id) >>=
                   true
                && self.hosts.index(id.value).is_Replica()
                && self.hosts.index(id.value).get_replica_variables().wf(c.hosts.index(id.value).get_replica_constants())
                )
            && forall(|id| #[auto_trigger] c.cluster_config.is_client(id) >>=
                   true
                && self.hosts.index(id.value).is_Client()
                && self.hosts.index(id.value).get_client_variables().wf(c.hosts.index(id.value).get_client_constants())
                )
            && forall(|id| #[auto_trigger] c.cluster_config.is_faulty_replica(id) >>=
                   true
                && self.hosts.index(id.value).is_FaultyReplica()
                )
        }
    }

    #[spec] fn Init(c:Constants, v:Variables) -> bool {
           true
        && v.wf(c)
        && forall(|id| #[auto_trigger] c.cluster_config.is_honest_replica(id)
                  >>= replica::init(c.hosts.index(id.value).get_replica_constants(), v.hosts.index(id.value).get_replica_variables()))
        && forall(|id| #[auto_trigger] c.cluster_config.is_client(id)
                  >>= client::init(c.hosts.index(id.value).get_client_constants(), v.hosts.index(id.value).get_client_variables()))
        && v.network.init()
    }
}

mod proof {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::seq::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
        crate::distributed_system::*,
    };

    #[spec] fn is_honest_replica(c:Constants, host_id: HostId) -> bool
    {
           true
        && c.wf()
        && c.cluster_config.is_honest_replica(host_id)
    }

    // Here's a predicate that will be very useful in constructing invariant conjuncts.
    #[spec] fn recorded_pre_prepares_recvd_came_from_network(c:Constants, v:Variables) -> bool {
           true
        && v.wf(c)
        && forall(|replica_idx, seq_id: SequenceID| 
               true
            && is_honest_replica(c, replica_idx)
            &&
                // assert Library.TriggerKeyInFullImap(seq_id, v.hosts[replica_idx].replicaVariables.workingWindow.prePreparesRcvd);
                v.hosts.index(replica_idx.value).get_replica_variables().working_window.pre_prepares_rcvd.map.index(seq_id).is_Some()
                >>= v.network.sent_msgs.contains(v.hosts.index(replica_idx.value).get_replica_variables().working_window.pre_prepares_rcvd.map.index(seq_id).value())
        )
    }

    #[spec] fn recorded_prepares_recvd_came_from_network(c:Constants, v:Variables, observer:HostId) -> bool
    {
           true
        && v.wf(c)
        && is_honest_replica(c, observer)
        && forall(|sender, seq_id| with_triggers!([v.network.sent_msgs.contains(msg), msg.sender == sender]) => {
            let msg = v.hosts.index(observer.value).get_replica_variables().working_window.prepares_rcvd.index(seq_id).map.index(sender);
                //&& assert Library.TriggerKeyInFullImap(seq_id, v.hosts[observer].replicaVariables.workingWindow.preparesRcvd);
            v.hosts.index(observer.value).get_replica_variables().working_window.prepares_rcvd.index(seq_id).map.contains(sender)
            >>= (
                // TODO(utaal): "`let` expressions are not supported here"
                //let msg = v.hosts.index(observer.value).get_replica_variables().working_window.prepares_rcvd.index(seq_id).index(sender);
                   true
                && v.network.sent_msgs.contains(msg)
                && msg.sender == sender
                && msg.payload.get_seq_id() == seq_id // The key we stored matches what is in the msg
                )
        })
    }

    

}

fn main() {}
