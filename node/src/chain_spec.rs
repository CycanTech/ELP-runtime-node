use cumulus_primitives::ParaId;
use sc_chain_spec::{ChainSpecExtension, ChainSpecGroup};
use sc_service::{ChainType, Properties};
use serde::{Deserialize, Serialize};
use sp_core::{sr25519, Pair, Public};
use sp_runtime::traits::{IdentifyAccount, Verify};
use std::collections::BTreeMap;

use parachain_runtime::{
        AccountId, AuraConfig, EVMConfig, EthereumConfig, GrandpaConfig, Signature
};
use parachain_runtime::ContractsConfig;

use sp_consensus_aura::sr25519::AuthorityId as AuraId;
use sp_finality_grandpa::AuthorityId as GrandpaId;

/// Specialized `ChainSpec` for the normal parachain runtime.
pub type ChainSpec = sc_service::GenericChainSpec<parachain_runtime::GenesisConfig, Extensions>;

/// Helper function to generate a crypto pair from seed
pub fn get_from_seed<TPublic: Public>(seed: &str) -> <TPublic::Pair as Pair>::Public {
	TPublic::Pair::from_string(&format!("//{}", seed), None)
		.expect("static values are valid; qed")
		.public()
}

/// The extensions for the [`ChainSpec`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecGroup, ChainSpecExtension)]
#[serde(deny_unknown_fields)]
pub struct Extensions {
	/// The relay chain of the Parachain.
	pub relay_chain: String,
	/// The id of the Parachain.
	pub para_id: u32,
}

impl Extensions {
	/// Try to get the extension from the given `ChainSpec`.
	pub fn try_get(chain_spec: &dyn sc_service::ChainSpec) -> Option<&Self> {
		sc_chain_spec::get_extension(chain_spec.extensions())
	}
}

type AccountPublic = <Signature as Verify>::Signer;

/// Helper function to generate an account ID from seed
pub fn get_account_id_from_seed<TPublic: Public>(seed: &str) -> AccountId
where
	AccountPublic: From<<TPublic::Pair as Pair>::Public>,
{
	AccountPublic::from(get_from_seed::<TPublic>(seed)).into_account()
}

/// Generate an Aura authority key.
pub fn authority_keys_from_seed(s: &str) -> (AuraId, GrandpaId) {
        (
                get_from_seed::<AuraId>(s),
                get_from_seed::<GrandpaId>(s),
        )
}

pub fn development_config(id: ParaId) -> ChainSpec {
	ChainSpec::from_genesis(
		// Name
		"Development",
		// ID
		"dev",
		ChainType::Local,
		move || {
			testnet_genesis(
                                // Initial PoA authorities
                                vec![
                                       authority_keys_from_seed("Alice"),
                                       authority_keys_from_seed("Bob"),
                                ],
                                // Sudo account
				get_account_id_from_seed::<sr25519::Public>("Alice"),
				vec![
					get_account_id_from_seed::<sr25519::Public>("Alice"),
					get_account_id_from_seed::<sr25519::Public>("Bob"),
					get_account_id_from_seed::<sr25519::Public>("Alice//stash"),
					get_account_id_from_seed::<sr25519::Public>("Bob//stash"),
				],
				id,
			)
		},
		vec![],
		None,
		None,
		None,
		Extensions {
			relay_chain: "rococo-dev".into(),
			para_id: id.into(),
		},
	)
}

pub fn local_testnet_config(id: ParaId) -> ChainSpec {

        let mut properties = Properties::new();
        properties.insert("tokenSymbol".into(), "ELPR".into());
        properties.insert("tokenDecimals".into(), 12.into());

        ChainSpec::from_genesis(
                "Everlasting Parallel Rococo", // Name
                "everlasting_parallel_rococo", // ID
		ChainType::Local,
		move || {
			testnet_genesis(
                                // Initial PoA authorities
                                vec![
                                       authority_keys_from_seed("Alice"),
                                       authority_keys_from_seed("Bob"),
                                ],
                                // Sudo account
				get_account_id_from_seed::<sr25519::Public>("Alice"),
                                // pre-funded account
				vec![
					get_account_id_from_seed::<sr25519::Public>("Alice"),
					get_account_id_from_seed::<sr25519::Public>("Bob"),
					get_account_id_from_seed::<sr25519::Public>("Charlie"),
					get_account_id_from_seed::<sr25519::Public>("Dave"),
					get_account_id_from_seed::<sr25519::Public>("Eve"),
					get_account_id_from_seed::<sr25519::Public>("Ferdie"),
					get_account_id_from_seed::<sr25519::Public>("Alice//stash"),
					get_account_id_from_seed::<sr25519::Public>("Bob//stash"),
					get_account_id_from_seed::<sr25519::Public>("Charlie//stash"),
					get_account_id_from_seed::<sr25519::Public>("Dave//stash"),
					get_account_id_from_seed::<sr25519::Public>("Eve//stash"),
					get_account_id_from_seed::<sr25519::Public>("Ferdie//stash"),
				],
				id,
			)
		},
		vec![], // Bootnodes
		None,   // Telemetry
		Some("dot"),  // Protocol ID
                Some(properties),
                Extensions {
                        relay_chain: "rococo-local-raw.json".into(),
                        para_id: id.into(),
                },
	)
}

fn testnet_genesis(
        initial_authorities: Vec<(AuraId, GrandpaId)>,
	root_key: AccountId,
	endowed_accounts: Vec<AccountId>,
	id: ParaId,
) -> parachain_runtime::GenesisConfig {
	parachain_runtime::GenesisConfig {
		frame_system: Some(parachain_runtime::SystemConfig {
			code: parachain_runtime::WASM_BINARY
				.expect("WASM binary was not build, please build it!")
				.to_vec(),
			changes_trie_config: Default::default(),
		}),
                pallet_aura: Some(AuraConfig {
                        authorities: initial_authorities.iter().map(|x| (x.0.clone())).collect(),
                }),
                pallet_grandpa: Some(GrandpaConfig {
                        authorities: initial_authorities.iter().map(|x| (x.1.clone(), 1)).collect(),
                }),
		pallet_balances: Some(parachain_runtime::BalancesConfig {
			balances: endowed_accounts
				.iter()
				.cloned()
				.map(|k| (k, 1 << 60))
				.collect(),
		}),
		pallet_sudo: Some(parachain_runtime::SudoConfig { key: root_key }),
		parachain_info: Some(parachain_runtime::ParachainInfoConfig { parachain_id: id }),
                pallet_contracts: Some(ContractsConfig {
                    current_schedule: pallet_contracts::Schedule {
                    ..Default::default()
                    },
                }),
                pallet_evm: Some(EVMConfig {
                        accounts: BTreeMap::new(),
                }),
                pallet_ethereum: Some(EthereumConfig {}),
	}
}
