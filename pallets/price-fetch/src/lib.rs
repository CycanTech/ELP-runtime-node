// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! <!-- markdown-link-check-disable -->
//! # Offchain Worker Example Pallet
//!
//! The Offchain Worker Example: A simple pallet demonstrating
//! concepts, APIs and structures common to most offchain workers.
//!
//! Run `cargo doc --package pallet-example-offchain-worker --open` to view this module's
//! documentation.
//!
//! - [`Config`]
//! - [`Call`]
//! - [`Pallet`]
//!
//!
//! ## Overview
//!
//! In this example we are going to build a very simplistic, naive and definitely NOT
//! production-ready oracle for BTC/USD price.
//! Offchain Worker (OCW) will be triggered after every block, fetch the current price
//! and prepare either signed or unsigned transaction to feed the result back on chain.
//! The on-chain logic will simply aggregate the results and store last `64` values to compute
//! the average price.
//! Additional logic in OCW is put in place to prevent spamming the network with both signed
//! and unsigned transactions, and custom `UnsignedValidator` makes sure that there is only
//! one unsigned transaction floating in the network.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_system::{
	self as system,
	offchain::{
		AppCrypto, CreateSignedTransaction, SendSignedTransaction, Signer,
	}
};
use frame_support::traits::{Currency};
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	offchain::{http, Duration},
};
use sp_std::vec::Vec;
use lite_json::json::JsonValue;
#[cfg(test)]
mod tests;

/// Defines application identifier for crypto keys of this module.
///
/// Every module that deals with signatures needs to declare its unique identifier for
/// its crypto keys.
/// When offchain worker is signing transactions it's going to request keys of type
/// `KeyTypeId` from the keystore and use the ones it finds to sign the transaction.
/// The keys can be inserted manually via RPC (see `author_insertKey`).
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"mypt");

/// Based on the above `KeyTypeId` we need to generate a pallet-specific crypto type wrappers.
/// We can use from supported crypto kinds (`sr25519`, `ed25519` and `ecdsa`) and augment
/// the types with this pallet-specific identifier.
pub mod crypto {
	use super::KEY_TYPE;
	use sp_runtime::{
		app_crypto::{app_crypto, sr25519},
		traits::Verify,
	};
	use sp_core::sr25519::Signature as Sr25519Signature;
	use frame_support::sp_runtime::{MultiSigner, MultiSignature};
	app_crypto!(sr25519, KEY_TYPE);

	pub struct TestAuthId;
	impl frame_system::offchain::AppCrypto<<Sr25519Signature as Verify>::Signer, Sr25519Signature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
	impl frame_system::offchain::AppCrypto<MultiSigner, MultiSignature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
}

pub use pallet::*;
use sp_runtime::app_crypto::sp_core::crypto::UncheckedFrom;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;
	use sp_runtime::app_crypto::sp_core::crypto::UncheckedFrom;
	use frame_support::traits::Currency;
	// use frame_support::dispatch::DispatchErrorWithPostInfo;
	// use frame_support::weights::PostDispatchInfo;


	//type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	/// This pallet's configuration trait
	#[pallet::config]
	pub trait Config: frame_system::Config  + pallet_contracts::Config + CreateSignedTransaction<Call<Self>> where
		<Self as frame_system::Config>::AccountId: AsRef<[u8]> + UncheckedFrom<Self::Hash>,
		<<Self as pallet_contracts::Config>::Currency as Currency<<Self as frame_system::Config>::AccountId>>::Balance: From<u128>,
	{
		/// The identifier type for an offchain worker.
		type AuthorityId: AppCrypto<Self::Public, Self::Signature>;

		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The overarching dispatch call type.
		type Call: From<Call<Self>>;
		type Currency: Currency<Self::AccountId>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
		where
			T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
			<<T as pallet_contracts::Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance: From<u128>,
	{
		fn offchain_worker(block_number: T::BlockNumber) {

			let parent_hash = <system::Pallet<T>>::block_hash(block_number - 1u32.into());
			log::info!("Current block: {:?} (parent hash: {:?})", block_number, parent_hash);

			let transaction_type = block_number % 5u32.into();
			if transaction_type == T::BlockNumber::from(1u32) {
				let res = Self::my_fetch_price_and_send_signed();
				if let Err(e) = res {
					log::error!("Error: {}", e);
				} else {
					let res = Self::my_call_contract_update();
					if let Err(e) = res {
						log::error!("Error: {}", e);
					}
				}
			}
		}
	}

	/// A public part of the pallet.
	#[pallet::call]
	impl<T: Config> Pallet<T> where
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
		<<T as pallet_contracts::Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance: From<u128>
	{
		#[pallet::weight(0)]
		fn my_submit_price(origin: OriginFor<T>, price: (u128,u128)) -> DispatchResultWithPostInfo {
			// Retrieve sender of the transaction.
			let who = ensure_signed(origin)?;
			// let signer = Signer::<T, T::AuthorityId>::all_accounts();
			// if !signer.can_sign() {
			// 	return Err(DispatchErrorWithPostInfo{post_info: PostDispatchInfo::from(()),error:DispatchError::Other("error account")});
			// }
			<ElpPrice<T>>::put(price.0);
			<ElcPrice<T>>::put(price.1);
			Self::deposit_event(Event::UpdatePrice(price, who));
			Ok(().into())
		}
		#[pallet::weight(0)]
		pub fn my_set_update_fn_para(origin: OriginFor<T>, address:T::AccountId, selector:Vec<u8>) -> DispatchResultWithPostInfo {
			// Retrieve sender of the transaction.
			let _who = ensure_signed(origin)?;
			// let signer = Signer::<T, T::AuthorityId>::all_accounts();
			// if !signer.can_sign() {
			// 	return Err(DispatchErrorWithPostInfo{post_info: PostDispatchInfo::from(()),error:DispatchError::Other("error account")});
			// }
			<ContractAddress<T>>::put(address);
			<Selector<T>>::put(selector);
			Ok(().into())
		}
		#[pallet::weight(10_000)]
		fn call_contract_update(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let _who = ensure_signed(origin)?;

			let elc_price = <ElcPrice<T>>::get();
			let elp_price = <ElpPrice<T>>::get();
			let address = <ContractAddress<T>>::get();
			let selector = <Selector<T>>::get();
			log::info!("=============================================================================================");
			log::info!("address:{:?},selector:{:?},elc_price:{},elp_price{}", address, selector, elc_price,elp_price);
			let encoded_elp = u128::encode(&elp_price);
			let encoded_elc = u128::encode(&elc_price);
			let input_data = [&selector[..], &encoded_elp[..], &encoded_elc[..]].concat();
			let exec_result = <pallet_contracts::Module<T>>::bare_call(_who, address.clone(), 0.into(), 600000000000000, input_data);
			match exec_result.exec_result {
				Ok(v) => {
					let result_val = bool::decode(&mut &v.data[..]);
					match result_val {
						Ok(b) => {
							log::info!("================update ok============{}",b);
						},
						Err(e) => { log::error!("{:?}",e)},
					}
				},
				Err(e) => {
					log::error!("================error============{:?}",e);
					log::error!("============gas================={}",exec_result.gas_consumed);
				},
			}

			Ok(().into())
		}

		// #[pallet::weight(10_000)]
		// fn call_contract_transfer(origin: OriginFor<T>, address: T::AccountId, selector: Vec<u8>,dest: T::AccountId,amount: BalanceOf<T>) -> DispatchResultWithPostInfo {
		// 	let who = ensure_signed(origin)?;
		//
		// 	let encoded_address = T::AccountId::encode(&dest);
		// 	let encoded_amount = BalanceOf::<T>::encode(&amount);
		// 	let input_data = [&selector[..], &encoded_address[..], &encoded_amount[..]].concat();
		// 	log::info!("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
		// 	let exec_result = <pallet_contracts::Module<T>>::bare_call(who, address.clone(), 0.into(), 600000000000000, input_data);
		// 	match exec_result.exec_result {
		// 		Ok(v) => {
		// 			let result_val = bool::decode(&mut &v.data[..]);
		// 			match result_val {
		// 				Ok(b) => {
		// 					log::info!("================get balance============{}",b);
		// 				},
		// 				Err(e) => { log::error!("jjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjj{:?}",e);},
		// 			}
		// 		},
		// 		Err(e) => {
		// 			log::error!("================get balance============{:?}",e);
		// 			log::error!("============gas================={}",exec_result.gas_consumed);
		// 		},
		// 	}
		//
		// 	Ok(().into())
		// }
		// #[pallet::weight(0)]
		// fn get_store(origin: OriginFor<T>, address: T::AccountId) -> DispatchResultWithPostInfo {
		// 	log::info!("mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm");
		// 	// Retrieve sender of the transaction.
		// 	let key_int: [u8; 32] = hex!("0000000000000000000000000000000000000000000000000000000000000000");
		// 	let res_int = <pallet_contracts::Module<T>>::get_storage(address.clone(), key_int);
		// 	match res_int {
		// 		Ok(Some(v)) => {
		// 			log::info!("============================{:?}",v);
		// 			let result_val = u128::decode(&mut &v[..]);
		// 			match result_val {
		// 				Ok(u) => {
		// 					log::info!("============================{}",u);
		// 				},
		// 				Err(_) => { },
		// 			}
		// 		},
		// 		Ok(None) => { },
		// 		Err(_) => { },
		// 	}
		// 	Ok(().into())
		// }
	}

	/// Events for the pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> where
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
		<<T as pallet_contracts::Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance: From<u128>
	{
		UpdatePrice((u128,u128), T::AccountId),
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> where
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
		<<T as pallet_contracts::Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance: From<u128>
	{
		type Call = Call<T>;

		/// Validate unsigned call to this module.
		///
		/// By default unsigned transactions are disallowed, but implementing the validator
		/// here we make sure that some particular calls (the ones produced by offchain worker)
		/// are being whitelisted and marked as valid.
		fn validate_unsigned(
			_source: TransactionSource,
			_call: &Self::Call,
		) -> TransactionValidity {
			InvalidTransaction::Call.into()
		}
	}

	//oracle price fetch contract address
	#[pallet::storage]
	#[pallet::getter(fn contract_address)]
	pub(super) type ContractAddress<T: Config> = StorageValue<_, T::AccountId, ValueQuery>;

	//oracle price fetch selector
	#[pallet::storage]
	#[pallet::getter(fn selector)]
	pub(super) type Selector<T: Config> = StorageValue<_, Vec<u8>, ValueQuery>;

	//elp price
	#[pallet::storage]
	#[pallet::getter(fn elp_price)]
	pub(super) type ElpPrice<T: Config> = StorageValue<_, u128, ValueQuery>;

	//elc price
	#[pallet::storage]
	#[pallet::getter(fn elc_price)]
	pub(super) type ElcPrice<T: Config> = StorageValue<_, u128, ValueQuery>;
}

impl<T: Config> Pallet<T>
	where
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
		<<T as pallet_contracts::Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance: From<u128>
{

	pub fn my_call_contract_update()  -> Result<(), &'static str>  {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC."
			)?
		}
		// Using `send_signed_transaction` associated type we create and submit a transaction
		// representing the call, we've just created.
		// Submit signed will return a vector of results for all accounts that were found in the
		// local keystore with expected `KEY_TYPE`.
		let results = signer.send_signed_transaction(
			|_account| {
				// Received price is wrapped into a call to `submit_price` public function of this pallet.
				// This means that the transaction, when executed, will simply call that function passing
				// `price` as an argument.
				Call::call_contract_update()
			}
		);

		for (acc, res) in &results {
			match res {
				Ok(()) => log::info!("[{:?}] update price ok!", acc.id),
				Err(e) => log::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
			}
		}

		Ok(())
	}

	fn my_fetch_price_and_send_signed() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC."
			)?
		}
		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::my_fetch_price().map_err(|_| "Failed to fetch price")?;

		// Using `send_signed_transaction` associated type we create and submit a transaction
		// representing the call, we've just created.
		// Submit signed will return a vector of results for all accounts that were found in the
		// local keystore with expected `KEY_TYPE`.
		let results = signer.send_signed_transaction(
			|_account| {
				// Received price is wrapped into a call to `submit_price` public function of this pallet.
				// This means that the transaction, when executed, will simply call that function passing
				// `price` as an argument.
				Call::my_submit_price(price)
			}
		);

		for (acc, res) in &results {
			match res {
				Ok(()) => log::info!("[{:?}] Submitted price of {} cents,{} cents", acc.id, price.0,price.1),
				Err(e) => log::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
			}
		}

		Ok(())
	}

	fn my_fetch_price() -> Result<(u128,u128), http::Error> {
		// We want to keep the offchain worker execution time reasonable, so we set a hard-coded
		// deadline to 2s to complete the external call.
		// You can also wait idefinitely for the response, however you may still get a timeout
		// coming from the host machine.
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(5_000));
		// Initiate an external HTTP GET request.
		// This is using high-level wrappers from `sp_runtime`, for the low-level calls that
		// you can find in `sp_io`. The API is trying to be similar to `reqwest`, but
		// since we are running in a custom WASM execution environment we can't simply
		// import the library here.
		let request = http::Request::get(
			"https://min-api.cryptocompare.com/data/price?fsym=DOT&tsyms=USD"
		);
		// We set the deadline for sending of the request, note that awaiting response can
		// have a separate deadline. Next we send the request, before that it's also possible
		// to alter request headers or stream body content in case of non-GET requests.
		let pending = request
			.deadline(deadline)
			.send()
			.map_err(|_| http::Error::IoError)?;
		// The request is already being processed by the host, we are free to do anything
		// else in the worker (we can send multiple concurrent requests too).
		// At some point however we probably want to check the response though,
		// so we can block current thread and wait for it to finish.
		// Note that since the request is being driven by the host, we don't have to wait
		// for the request to have it complete, we will just not read the response.
		let response = pending.try_wait(deadline)
			.map_err(|_| http::Error::DeadlineReached)??;
		// Let's check the status code before we proceed to reading the response.
		if response.code != 200 {
			log::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown);
		}
		// Note that the return object allows you to read the body in chunks as well
		// with a way to control the deadline.
		let body = response.body().collect::<Vec<u8>>();
		// Create a str slice from the body.
		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
			log::warn!("No UTF8 body");
			http::Error::Unknown
		})?;
		let price = match Self::my_parse_price(body_str) {
			Some(price) => Ok(price),
			None => {
				log::warn!("Unable to extract price from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			}
		}?;

		log::warn!("Got price: {} cents,{} cents", price.0,price.1);

		Ok(price)
	}

	fn my_parse_price(price_str: &str) -> Option<(u128,u128)> {
		let val = lite_json::parse_json(price_str);
		let price = val.ok().and_then(|v| match v {
			JsonValue::Object(obj) => {
				let mut elp_chars = "USD".chars();
				obj.into_iter()
					.find(|(k, _)| k.iter().all(|k| Some(*k) == elp_chars.next()))
					.and_then(|v| match v.1 {
						JsonValue::Number(number) => Some(number),
						_ => None,
					})
			},
			_ => None
		})?;
		let exp = price.fraction_length.checked_sub(2).unwrap_or(0);
		let elp_price = price.integer as u32 * 100 + (price.fraction / 10_u64.pow(exp)) as u32;
		let val2 = lite_json::parse_json(price_str);
		let price = val2.ok().and_then(|v| match v {
			JsonValue::Object(obj) => {
				let mut elc_chars = "USD".chars();
				obj.into_iter()
					.find(|(k, _)| k.iter().all(|k| Some(*k) == elc_chars.next()))
					.and_then(|v| match v.1 {
						JsonValue::Number(number) => Some(number),
						_ => None,
					})
			},
			_ => None
		})?;
		let exp = price.fraction_length.checked_sub(2).unwrap_or(0);
		let elc_price = price.integer as u32 * 100 + (price.fraction / 10_u64.pow(exp)) as u32;
		Some((elp_price as u128, elc_price as u128))
	}
}