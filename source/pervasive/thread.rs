#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

#[macro_export]
#[stable(feature = "rust1", since = "1.0.0")]
#[cfg_attr(not(test), rustc_diagnostic_item = "println_macro")]
#[allow_internal_unstable(print_internals, format_args_nl)]
macro_rules! println {
    () => {
    };
    ($($arg:tt)*) => {{
    }};
}

verus! {

pub trait Spawnable<Ret: Sized> : Sized {
    spec fn pre(self) -> bool;

    spec fn post(self, ret: Ret) -> bool;
    
    exec fn run(self) -> (r: Ret)
        requires self.pre(),
        ensures self.post(r);
}

#[verifier(external_body)]
pub struct JoinHandle<#[verifier(maybe_negative)] Ret>
{
    handle: core::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret>
{
    fndecl!(pub fn predicate(&self, ret: Ret) -> bool);

    #[verifier(external_body)]
    pub fn join(self) -> Result<Ret, ()>
    {
        ensures(|r: Result<Ret, ()>|
            r.is_Ok() ==> self.predicate(r.get_Ok_0()));

        let res = core::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            match self.handle.join() {
                Ok(r) => Result::Ok(r),
                Err(_) => Result::Err(()),
            }
        }));
        match res {
            Ok(res) => res,
            Err(_) => {
                println!("panic on join");
                core::process::abort();
            }
        }
    }
}

#[verifier(external_body)]
pub fn spawn<Param: Spawnable<Ret> + Send + 'static, Ret: Send + 'static>(p: Param) -> JoinHandle<Ret> 
{
    requires(p.pre());
    ensures(|handle: JoinHandle<Ret>|
        forall(|ret: Ret| handle.predicate(ret) ==> p.post(ret)));

    let res = core::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
        let handle = core::thread::spawn(move || p.run());
        JoinHandle { handle }
    }));
    match res {
        Ok(res) => res,
        Err(_) => {
            println!("panic on spawn");
            core::process::abort();
        }
    }
}

} // verus!
