use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

mod vtab;

fn main() {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "rusqlite-vtab-unnest=info".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    println!("Hello, world!");
}
