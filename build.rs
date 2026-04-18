fn main() {
    let mut b = cc::Build::new();
    b.file("mldsa/mldsa_native.c")
        .include("mldsa")
        .define("MLD_CONFIG_PARAMETER_SET", "87")
        .define("MLD_CONFIG_NAMESPACE_PREFIX", "bubbler_mldsa87")
        .define("MLD_CONFIG_NO_RANDOMIZED_API", None)
        .define("MLD_CONFIG_NO_SUPERCOP", None)
        .flag_if_supported("-std=c99")
        .flag_if_supported("-O3")
        .flag_if_supported("-fvisibility=hidden")
        .warnings(false);

    b.compile("bubbler_mldsa87");

    println!("cargo:rerun-if-changed=mldsa");
    println!("cargo:rerun-if-changed=build.rs");
}
