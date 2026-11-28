//! Load-only invalid signatures; the ordinary manifest is the control in this DLL.
use cranelisp_platform::*;

macro_rules! fixture {
    ($module:ident, $name:literal, $cl:literal, $sig:literal) => {
        mod $module {
            use super::*;
            static HOST: HostContext = HostContext::new();
            pub extern "C" fn ordinary() -> CLIO<CLInt> { CLIO::pure(CLInt::from(42)) }
            declare_platform! {
                name: $name, version: "0.1.0", host: HOST,
                functions: [ ordinary {
                    cl_name: $cl, sig: $sig, doc: "S125 load-signature fixture",
                    params: [], scheduling: SchedulingClass::Commutative,
                } ]
            }
        }
    }
}
fixture!(param, "fnparam", "bad-param", "(Fn [(Fn [primitives/Int] primitives/Int)] (primitives/IO primitives/Int))");
fixture!(result, "fnresult", "bad-result", "(Fn [primitives/Int] (primitives/IO (Fn [primitives/Int] primitives/Int)))");
fixture!(field, "fnfield", "bad-field", "(Fn [holder/Callback] (primitives/IO primitives/Int))");
fixture!(good, "fngood", "ordinary", "(Fn [] (primitives/IO primitives/Int))");
