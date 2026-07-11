//! CLI entry point.
//!
//! Each mode is selected by a `--combine_rules` / `--enum_wheels` / … switch
//! (modes are independent, not mutually exclusive), and the required options for
//! each mode are validated up front.

use clap::Parser;
use std::path::Path;

// The hot path allocates `vmap`/`dmap` scratch per `homomorphism` call (millions of
// times), where the system allocator dominates. mimalloc's thread-local
// free-list makes those allocations cheap.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// near-linear 4CT computer checks (Rust port).
#[derive(Parser, Debug)]
#[command(
    name = "main",
    about = "Combine discharging rules and enumerate/verify cartwheels"
)]
struct Cli {
    // NB: flag names use underscores to match the documented CLI / README exactly
    // (clap would otherwise kebab-case them).
    /// Combine rules (Lemma A.1 / A.2).
    #[arg(long = "combine_rules")]
    combine_rules: bool,
    /// Enumerate wheels (Lemma A.3, step 1).
    #[arg(long = "enum_wheels")]
    enum_wheels: bool,
    /// Enumerate cartwheels (Lemma A.3, step 2).
    #[arg(long = "enum_cartwheels")]
    enum_cartwheels: bool,
    /// Combine cartwheels with a degree-8 center (Lemma A.4).
    #[arg(long = "check_deg8")]
    check_deg8: bool,
    /// Combine cartwheels to form a 7-triangle (Lemma A.5).
    #[arg(long = "check_7triangle")]
    check_7triangle: bool,
    /// Combine cartwheels with a degree-7 center (Lemma A.6).
    #[arg(long = "check_deg7")]
    check_deg7: bool,

    /// A directory containing configuration files.
    #[arg(short = 'C', long = "confdir")]
    confdir: Option<String>,
    /// A directory containing rule files.
    #[arg(short = 'R', long = "ruledir")]
    ruledir: Option<String>,
    /// A directory containing combined rule files.
    #[arg(short = 'S', long = "combined_ruledir")]
    combined_ruledir: Option<String>,
    /// A directory containing cartwheel files.
    #[arg(short = 'W', long = "cartwheeldir")]
    cartwheeldir: Option<String>,
    /// A wheel file.
    #[arg(short = 'w', long = "wheel")]
    wheel: Option<String>,
    /// Degree of the center vertex of wheels.
    #[arg(short = 'd', long = "degree")]
    degree: Option<i32>,
    /// Output directory.
    #[arg(short = 'o', long = "outdir")]
    outdir: Option<String>,
    /// Verbosity: 1 for debug, 2 for trace.
    #[arg(short = 'v', long = "verbosity", default_value_t = 0)]
    verbosity: i32,
}

/// Require an option to be present, with a `Specify {name}.` error otherwise.
fn require<'a>(opt: &'a Option<String>, name: &str) -> anyhow::Result<&'a str> {
    opt.as_deref()
        .ok_or_else(|| anyhow::anyhow!("Specify {name}."))
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let level = match cli.verbosity {
        1 => tracing::Level::DEBUG,
        2 => tracing::Level::TRACE,
        _ => tracing::Level::INFO,
    };
    tracing_subscriber::fmt().with_max_level(level).init();

    if cli.combine_rules {
        let confdir = require(&cli.confdir, "confdir")?;
        let ruledir = require(&cli.ruledir, "ruledir")?;
        let outdir = require(&cli.outdir, "outdir")?;
        combine::rule::run_combine_rules(Path::new(confdir), Path::new(ruledir), Path::new(outdir));
    }
    if cli.enum_wheels {
        let degree = cli
            .degree
            .ok_or_else(|| anyhow::anyhow!("Specify degree."))?;
        let confdir = require(&cli.confdir, "confdir")?;
        let ruledir = require(&cli.ruledir, "ruledir")?;
        let combined_ruledir = require(&cli.combined_ruledir, "combined_ruledir")?;
        let outdir = require(&cli.outdir, "outdir")?;
        combine::cartwheel::run_enum_wheels(
            degree as usize,
            Path::new(confdir),
            Path::new(ruledir),
            Path::new(combined_ruledir),
            Path::new(outdir),
        );
    }
    if cli.enum_cartwheels {
        let wheel = require(&cli.wheel, "wheel")?;
        let confdir = require(&cli.confdir, "confdir")?;
        let ruledir = require(&cli.ruledir, "ruledir")?;
        let combined_ruledir = require(&cli.combined_ruledir, "combined_ruledir")?;
        let outdir = require(&cli.outdir, "outdir")?;
        combine::cartwheel::run_enum_cartwheels(
            Path::new(wheel),
            Path::new(confdir),
            Path::new(ruledir),
            Path::new(combined_ruledir),
            Path::new(outdir),
        );
    }
    if cli.check_deg8 {
        let cartwheeldir = require(&cli.cartwheeldir, "cartwheeldir")?;
        let confdir = require(&cli.confdir, "confdir")?;
        combine::combine_cartwheel::run_check_deg8(Path::new(cartwheeldir), Path::new(confdir));
    }
    if cli.check_7triangle {
        let cartwheeldir = require(&cli.cartwheeldir, "cartwheeldir")?;
        let confdir = require(&cli.confdir, "confdir")?;
        combine::combine_cartwheel::run_check_7triangle(
            Path::new(cartwheeldir),
            Path::new(confdir),
        );
    }
    if cli.check_deg7 {
        let cartwheeldir = require(&cli.cartwheeldir, "cartwheeldir")?;
        let confdir = require(&cli.confdir, "confdir")?;
        combine::combine_cartwheel::run_check_deg7(Path::new(cartwheeldir), Path::new(confdir));
    }
    Ok(())
}
