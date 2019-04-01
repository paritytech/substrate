use crate::chain_spec;
use crate::service;
use futures::{future, sync::oneshot, Future};
use log::info;
use std::cell::RefCell;
use std::ops::Deref;
pub use substrate_cli::{error, IntoExit, VersionInfo};
use substrate_cli::{informant, parse_and_execute, NoCustom};
use substrate_service::{Roles as ServiceRoles, ServiceFactory};
use tokio::runtime::Runtime;

/// Parse command line arguments into service configuration.
pub fn run<I, T, E>(args: I, exit: E, version: VersionInfo) -> error::Result<()>
where
    I: IntoIterator<Item = T>,
    T: Into<std::ffi::OsString> + Clone,
    E: IntoExit,
{
    parse_and_execute::<service::Factory, NoCustom, NoCustom, _, _, _, _, _>(
        load_spec,
        &version,
        "substrate-node",
        args,
        exit,
        |exit, _custom_args, config| {
            info!("{}", version.name);
            info!("  version {}", config.full_version());
            info!("  by {}, 2017, 2018", version.author);
            info!("Chain specification: {}", config.chain_spec.name());
            info!("Node name: {}", config.name);
            info!("Roles: {:?}", config.roles);
            let runtime = Runtime::new().map_err(|e| format!("{:?}", e))?;
            let executor = runtime.executor();
            match config.roles {
                ServiceRoles::LIGHT => run_until_exit(
                    runtime,
                    service::Factory::new_light(config, executor)
                        .map_err(|e| format!("{:?}", e))?,
                    exit,
                ),
                _ => run_until_exit(
                    runtime,
                    service::Factory::new_full(config, executor).map_err(|e| format!("{:?}", e))?,
                    exit,
                ),
            }
            .map_err(|e| format!("{:?}", e))
        },
    )
    .map_err(Into::into)
    .map(|_| ())
}

fn load_spec(id: &str) -> Result<Option<chain_spec::ChainSpec>, String> {
    Ok(match chain_spec::Alternative::from(id) {
        Some(spec) => Some(spec.load()?),
        None => None,
    })
}

fn run_until_exit<T, C, E>(mut runtime: Runtime, service: T, e: E) -> error::Result<()>
where
    T: Deref<Target = substrate_service::Service<C>>,
    C: substrate_service::Components,
    E: IntoExit,
{
    let (exit_send, exit) = exit_future::signal();

    let executor = runtime.executor();
    informant::start(&service, exit.clone(), executor.clone());

    let _ = runtime.block_on(e.into_exit());
    exit_send.fire();

    // we eagerly drop the service so that the internal exit future is fired,
    // but we need to keep holding a reference to the global telemetry guard
    let _telemetry = service.telemetry();
    drop(service);
    Ok(())
}

// handles ctrl-c
pub struct Exit;
impl IntoExit for Exit {
    type Exit = future::MapErr<oneshot::Receiver<()>, fn(oneshot::Canceled) -> ()>;
    fn into_exit(self) -> Self::Exit {
        // can't use signal directly here because CtrlC takes only `Fn`.
        let (exit_send, exit) = oneshot::channel();

        let exit_send_cell = RefCell::new(Some(exit_send));
        ctrlc::set_handler(move || {
            if let Some(exit_send) = exit_send_cell
                .try_borrow_mut()
                .expect("signal handler not reentrant; qed")
                .take()
            {
                exit_send.send(()).expect("Error sending exit notification");
            }
        })
        .expect("Error setting Ctrl-C handler");

        exit.map_err(drop)
    }
}
