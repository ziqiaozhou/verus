mod pervasive;
#[allow(unused_imports)]
use builtin::*;
use pervasive::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use pervasive::seq::*;
#[allow(unused_imports)]
use pervasive::seq_lib::*;
use pervasive::vec::*;

// TODO: Don't use subtraction here
const max_size_t:usize = 0x1_0000_0000  - 1;
const max_uint64:u64 = 0x1_0000_0000_0000_0000   - 1;
const size_block:u32 = 16;

fndecl!(fn aead_encrypt(k:Seq<u8>, n:Seq<u8>, m:Seq<u8>, aad:Seq<u8>) -> Seq<u8>);

#[exec]
#[verifier(external_body)]
fn aead_encrypt_impl(k:&Vec<u8>, n:&Vec<u8>, m:&Vec<u8>, aad:&Vec<u8>) -> Vec<u8>
{
    requires([k.len() == 32, 
              n.len() == 12,
              m.len() <= max_size_t,
             ]);
    ensures(|c:Vec<u8>| [ equal(c.view(), aead_encrypt(k.view(), n.view(), m.view(), aad.view())) ]);
// TODO
//    #[no_mangle]
//    pub extern "C" fn callable_from_c(x: i32) -> bool {
//        x % 3 == 0
//    }
//    #[link(name = "my_c_library")]
//    extern "C" {
//        fn my_c_function(x: i32) -> bool;
//    }
    panic!("Connect me to EverCrypt please")
}

#[spec]
#[verifier(external_body)]
fn random_byte(index:nat) -> u8 
{
    42
}

#[proof]
#[verifier(unforgeable)]
struct Indexer {
    #[spec] i:nat
}

#[exec]
#[verifier(external_body)]
// TODO: What's the difference between lists of requires/ensures and conjunctions thereof?
//       I eventually deduced that lists provide more fine-grained error reporting
fn sample(#[spec] index:&mut Indexer, buffer:&mut Vec<u8>, count:u32) 
{
    requires(old(buffer).len() >= count);
    ensures([
        buffer.len() >= count,
        forall(|i:nat| i < count >>= buffer.index(i) == random_byte(old(index).i + i)),
        index.i == old(index).i + count
    ]);
}

struct Config {
    skA:Seq<u8>,
    pkB:Seq<u8>,
    idA:Seq<u8>,
    idB:Seq<u8>,
}

// TODO: Convert to Impl for Config
#[spec]
fn config_valid(c:Config) -> bool 
{
    c.skA.len() == 32 && 
    c.pkB.len() == 32 && 
    c.idA.len() == 24 && 
    c.idB.len() == 24
}

#[is_variant] #[derive(Structural, PartialEq, Eq)]
enum Stage { Init , Accept , Final }

struct Session {
    s:Stage,
    nA:Seq<u8>,
    nB:Seq<u8>,
}

// TODO: Would be nice to derive this
// TODO: Replace with equal(.,.) instead of ==
#[spec]
fn session_equal(s0:Session, s1:Session) -> bool
{
    s0.s == s1.s && equal(s0.nA, s1.nA) && equal(s0.nB, s1.nB)
}

#[spec]
fn session_valid(s:Session) -> bool
{
    s.nA.len() == 12 &&
    s.nB.len() == 12 &&
    (s.s.is_Init() >>= equal(s.nA, Seq::new(12, |i:int| 0)) &&
                       equal(s.nB, Seq::new(12, |i:int| 0))) &&
    (s.s.is_Accept() >>= equal(s.nB, Seq::new(12, |i:int| 0)))
}

#[spec]
fn nsl_client1(c:Config, session:Session, random_tape:Seq<u8>) -> (Seq<u8>, Session)
{
//    requires(random_tape.len() == 24 &&
//             config_valid(c) &&
//             session_valid(session) &&
//             session.s.is_Init());
//    ensures(|r:(Seq<u8>,Session)| session_valid(r.1));
    // TODO: It would be nice to be able to name tuple elements in the ensures clause
    //ensures(|(c, new_session):(Seq<u8>,Session)| session_valid(new_session));
    if random_tape.len() == 24 &&
       config_valid(c) &&
       session_valid(session) &&
       session.s.is_Init() {
        let nA = random_tape.subrange(0, 12);
        let enc_nonce = random_tape.subrange(12, 24);
        let c = aead_encrypt(c.pkB, enc_nonce, c.idA.add(nA), Seq::empty());
        (c, Session { s : Stage::Accept, nA : nA, nB : session.nB })
    } else {
        arbitrary()
    }
}

struct ConfigImpl {
    skA : Vec<u8>,
    pkB : Vec<u8>,
    idA : Vec<u8>,
    idB : Vec<u8>,
}

struct SessionImpl {
    s : Stage,
    nA : Vec<u8>,
    nB : Vec<u8>,
}

// TODO: Impls for types
#[spec]
fn session_impl_valid(s:SessionImpl) -> bool
{
    s.nA.view().len() == 12 && s.nB.view().len() == 12
}

#[spec]
fn config_impl_I(c:ConfigImpl) -> Config 
{
    Config { 
        skA : c.skA.view(),
        pkB : c.pkB.view(),
        idA : c.idA.view(),
        idB : c.idB.view(),
    }
}

#[spec]
fn session_impl_I(s:SessionImpl) -> Session
{
    Session {
        s : s.s,
        nA : s.nA.view(),
        nB : s.nB.view(),
    }
}

#[exec]
//#[verifier(external_body)]
// TODO: Why can't dst be marked &mut?
fn memcpy(src:&Vec<u8>, dst_in:Vec<u8>, start:usize, end:usize, dst_start:usize) -> Vec<u8>
{
    requires(0 <= start && start <= end && end <= src.view().len() &&
             // TODO: Would be nice to use usize::MAX here
             dst_start as int + (end - start) as int <= max_size_t && // NOTE: Not required in Dafny version
             0 <= dst_start && (dst_start as int + (end - start) as int) as int <= dst_in.view().len() &&
             dst_in.view().len() <= max_uint64);
    // TODO: Why does Verus/Rust need a type annotation on the parameter?
    ensures(|dst:Vec<u8>| [dst.view().len() == dst_in.view().len(),
            equal(src.view().subrange(start, end), dst.view().subrange(dst_start, (dst_start as int + (end - start) as int))), 
            forall(|i| 0 <= i && i < dst_start as int >>= dst.view().index(i) == dst_in.view().index(i)), 
            forall(|i| dst_start + (end - start) <= i && i < dst.len() >>= dst.view().index(i) == dst_in.view().index(i))]);

    let mut i = 0;
    let mut dst = dst_in;
    let len:usize = end - start;

    while i < len {
        invariant([
            0 <= i && i <= len,
            // NOTE: Next 5 lines were not needed for Dafny's while loop
            len == end - start,
            0 <= start && start <= end && end <= src.view().len(),
            dst_start as int + (end - start) as int <= max_size_t, 
            0 <= dst_start && (dst_start as int + (end - start) as int) as int <= dst.view().len(),
            dst.view().len() == dst_in.view().len(),
            /////////////////////////
            dst_start as int + i as int <= dst_start as int + len as int && dst_start as int + len as int <= dst.view().len(),
            forall(|k| dst_start <= k && k < dst_start + i >>= dst.view().index(k) == src.view().index(((k - dst_start) + start) as int)),
            forall(|j| 0 <= j && j < dst_start as int >>= dst.view().index(j) == dst_in.view().index(j)),
            forall(|j| (i + dst_start) as int <= j && j < dst.view().len() >>= dst.view().index(j) == dst_in.view().index(j))
        ]);
        let x = *src.index(start + i);

        assert(dst_start as int <= (dst_start as int) + (i as int));        // TODO: Surprising that this failed without the `as int`
        assert(i < len);
        assert(dst_start as int + len as int <= max_size_t);
        assert(dst_start + len >= dst_start && dst_start + len >= len);
        assert(dst_start + i < dst_start + len);
        assert(((dst_start + i) as int) < ((dst_start + dst.view().len()) as int));
        dst = dst.set(dst_start + i, x);
        i = i + 1;
    }
    assert(src.view().subrange(start, end).len() == dst.view().subrange(dst_start, (dst_start as int + (end - start) as int)).len());
    #[spec] let lhs = src.view().subrange(start, end);
    #[spec] let rhs = dst.view().subrange(dst_start, (dst_start as int + (end - start) as int));
    assert (lhs.len() == rhs.len());
    assert_forall_by(|k:int| {
        ensures(0 <= k && k < lhs.len() >>= lhs.index(k) == rhs.index(k));
        
    });
    assert(forall(|k:int| 0 <= k && k < lhs.len() >>= lhs.index(k) == rhs.index(k)));
    assert(lhs.ext_equal(rhs));     // TODO: Had to discover the need for this via the asserts above and below.  Coming from Dafny, I expected the next line to have the same effect as this one
    assert(equal(lhs, rhs));
    assert(equal(src.view().subrange(start, end), dst.view().subrange(dst_start, (dst_start as int + (end - start) as int))));
    dst
}

#[spec]
fn make_random_seq(start:nat, count:nat) -> Seq<u8>
{
    Seq::new(count, |i:int| random_byte((start + i) as nat))
}

#[exec]
// TODO: Idiomatically, we would typically want `index` and `out` to be mutated in place
fn nsl_client1_impl(c:&ConfigImpl, s:&mut SessionImpl, #[proof] index:&mut Indexer, out:Vec<u8>,
                    enc_nonce:Vec<u8>, plaintext:Vec<u8>, aad:Vec<u8>) -> Vec<u8>
{
    // Had to add a bunch of dereferences (e.g., *c, *s).  Could that be inferred?
    requires([old(s).s.is_Init(),
              config_valid(config_impl_I(*c)),
              session_impl_valid(*old(s)),
              session_valid(session_impl_I(*old(s))),
              enc_nonce.view().len() == 12,
              plaintext.view().len() == 36,
              aad.view().len() == 0,
              out.view().len() >= 64]);
    ensures(|t:Vec<u8>|[
             session_impl_valid(*s),
             session_valid(session_impl_I(*s)),
             index.i == old(index).i + 24,
             {#[spec] let (c, new_s) = nsl_client1(config_impl_I(*c), session_impl_I(*old(s)), make_random_seq(old(index).i, 24));
              equal(t.view().subrange(0, 64), c) && session_equal(session_impl_I(*s), new_s) }
            ]);
 
  // TODO: In Dafny, we allocate enc_nonce, plaintext, and aad.  For now, added them as arguments.
  // let mut enc_nonce = Vec { vec : std::vec::Vec::new(/*12*/) };
  let nA_holder = s.nA;
  sample(&mut index, &mut enc_nonce, 12);
  // TODO: Wanted to write:
  //    sample(&mut index_mut, &mut s.nA, 12);
  // but complex arguments to &mut are not currently supported, so I wrote this instead:
  sample(&mut index, &mut nA_holder, 12);
  *s = SessionImpl { s : s.s, nA : nA_holder, nB : s.nB };        // Update nA field

  //let mut plaintext = Vec { vec : std::vec::Vec::new(/*36*/) };
  let mut plaintext_holder = plaintext;
  plaintext_holder = memcpy(&c.idA, plaintext_holder, 0, 24, 0);
  plaintext_holder = memcpy(&s.nA,  plaintext_holder, 0, 12, 24);
  
  //let mut aad = Vec { vec : std::vec::Vec::new() };
  let c = aead_encrypt_impl(&c.pkB, &enc_nonce, &plaintext, &aad);
  // TODO: Wanted to write:
  //    s.s = Stage::Accept;
  // but field updates are not currently supported, so I wrote this instead:
  *s = SessionImpl { s : s.s, .. *s };

  memcpy(&c, out, 0, 64, 0)
}


fn main() {
}
