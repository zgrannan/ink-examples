extern crate prusti_contracts;
mod erc20 {
    use prusti_contracts::*;

    #[extern_spec]
    impl Default for Balance {
        #[pure]
        #[ensures(result == 0)]
        fn default() -> Self;
    }

    #[extern_spec]
    impl<T: Default> Option<T> {
        #[pure]
        #[ensures(result == matches!(self, None))]
        fn is_none(&self) -> bool;

        #[pure]
        #[ensures(result == matches!(self, Some(_)))]
        fn is_some(&self) -> bool;

        #[pure]
        #[requires(self.is_some())]
        #[ensures(self === Some(result))]
        fn unwrap(self) -> T;

        #[pure]
        #[ensures(self.is_some() ==> result === self.unwrap())]
        #[ensures(!self.is_some() ==> result === Default::default())]
        fn unwrap_or_default(self) -> T;
    }

    type AccountId = u32;
    type Balance = u64;

    #[resource_kind]
    struct Money(AccountId);

    #[resource_kind]
    struct Allowance(AccountId, AccountId);

    struct Mapping<K, V>(u32, std::marker::PhantomData<(K, V)>);

    impl<K, V: Copy> Mapping<K, V> {
        #[trusted]
        #[ensures(forall(|k : &K| result.get(k) === None))]
        #[ensures(forall(|k : &K| !result.get(k).is_some()))]
        fn new() -> Self {
            unimplemented!()
        }
    }

    // impl <T, U: Copy> Default for Mapping<T, U> {
    //     fn default() -> Self {
    //         Mapping::new()
    //     }
    // }

    impl<T, U: Copy> Mapping<T, U> {
        #[trusted]
        #[ensures(self.get(key) === Some(*value))]
        #[ensures(self.get(key).is_some())]
        #[ensures(self.get(key).unwrap() === value)]
        #[ensures(forall(|k : &T| k !== key ==> self.get(k) === old(self.get(k))))]
        fn insert(&mut self, key: &T, value: &U) {
            unimplemented!()
        }

        #[pure]
        #[trusted]
        fn get(&self, key: &T) -> Option<U> {
            unimplemented!()
        }
    }
    // use ink::storage::Mapping;

    #[invariant_twostate(
        self.env.0 == old(self.env.0)
    )]
    #[invariant_twostate(
        forall(|owner: AccountId| {
            PermAmount::from(self.balance_of(owner)) - old(PermAmount::from(self.balance_of(owner)))
            == holds(Money(owner)) - old(holds(Money(owner)))
        })
    )]
    #[invariant_twostate(
        forall(|a1: &AccountId, a2: &AccountId| {
            PermAmount::from(self.allowance_impl(a1, a2)) - old(PermAmount::from(self.allowance_impl(a1, a2)))
            == holds(Allowance(*a1, *a2)) - old(holds(Allowance(*a1, *a2)))
        })
    )]
    pub struct Erc20 {
        /// Total token supply.
        total_supply: Balance,
        /// Mapping from owner to number of owned token.
        balances: Mapping<AccountId, Balance>,
        /// Mapping of the token amount which an account is allowed to withdraw
        /// from another account.
        allowances: Mapping<(AccountId, AccountId), Balance>,

        env: Env,
    }

    /// Event emitted when a token transfer occurs.
    pub struct Transfer {
        from: Option<AccountId>,
        to: Option<AccountId>,
        value: Balance,
    }

    /// Event emitted when an approval occurs that `spender` is allowed to withdraw
    /// up to the amount of `value` tokens from `owner`.
    pub struct Approval {
        owner: AccountId,
        spender: AccountId,
        value: Balance,
    }

    pub enum Error {
        /// Returned if not enough balance to fulfill a request is available.
        InsufficientBalance,
        /// Returned if not enough allowance to fulfill a request is available.
        InsufficientAllowance,
    }

    /// The ERC-20 result type.
    pub type Result<T> = core::result::Result<T, Error>;

    struct Env(AccountId);

    impl Env {
        #[pure]
        fn caller(&self) -> AccountId {
            self.0
        }
        fn emit_event<T>(&self, event: T) {}
    }

    impl Erc20 {

        #[pure]
        fn env(&self) -> &Env {
            &self.env
        }

        /// Creates a new ERC-20 contract with the specified initial supply.
        #[ensures(resource(Money(caller), total_supply))]
        #[ensures(result.balance_of_impl(&caller) == total_supply)]
        #[ensures(forall(|other: AccountId| other !== caller ==> result.balance_of_impl(&other) == 0))]
        #[ensures(forall(|a1: AccountId, a2: AccountId| result.allowance_impl(&a1, &a2) == 0))]
        pub fn new(total_supply: Balance, caller: AccountId) -> Self {
            let mut balances = Mapping::new();
            balances.insert(&caller, &total_supply);
            produce!(resource(Money(caller), total_supply));
            Self {
                total_supply,
                balances,
                allowances: Mapping::new(),
                env: Env(caller),
            }
        }

        /// Returns the total token supply.
        pub fn total_supply(&self) -> Balance {
            self.total_supply
        }

        /// Returns the account balance for the specified `owner`.
        ///
        /// Returns `0` if the account is non-existent.
        #[pure]
        pub fn balance_of(&self, owner: AccountId) -> Balance {
            self.balance_of_impl(&owner)
        }

        /// Returns the account balance for the specified `owner`.
        ///
        /// Returns `0` if the account is non-existent.
        ///
        /// # Note
        ///
        /// Prefer to call this method over `balance_of` since this
        /// works using references which are more efficient in Wasm.
        #[pure]
        #[ensures(!self.balances.get(owner).is_some() ==> (result == 0))]
        fn balance_of_impl(&self, owner: &AccountId) -> Balance {
            if self.balances.get(owner).is_some() {
                self.balances.get(owner).unwrap()
            } else {
                0
            }
        }

        /// Returns the amount which `spender` is still allowed to withdraw from `owner`.
        ///
        /// Returns `0` if no allowance has been set.
        #[pure]
        pub fn allowance(&self, owner: AccountId, spender: AccountId) -> Balance {
            self.allowance_impl(&owner, &spender)
        }

        /// Returns the amount which `spender` is still allowed to withdraw from `owner`.
        ///
        /// Returns `0` if no allowance has been set.
        ///
        /// # Note
        ///
        /// Prefer to call this method over `allowance` since this
        /// works using references which are more efficient in Wasm.
        #[inline]
        #[pure]
        #[ensures(!self.allowances.get(&(*owner, *spender)).is_some() ==> (result == 0))]
        fn allowance_impl(&self, owner: &AccountId, spender: &AccountId) -> Balance {
            if self.allowances.get(&(*owner, *spender)).is_some() {
                self.allowances.get(&(*owner, *spender)).unwrap()
            } else {
                0
            }
        }

        /// Transfers `value` amount of tokens from the caller's account to account `to`.
        ///
        /// On success a `Transfer` event is emitted.
        ///
        /// # Errors
        ///
        /// Returns `InsufficientBalance` error if there are not enough tokens on
        /// the caller's account balance.
        #[requires(self.balance_of(self.env().caller()) >= value ==> resource(Money(self.env().caller()), value))]
        #[ensures(old(self.balance_of(self.env().caller())) >= value ==> resource(Money(to), value))]
        #[ensures(old(self.balance_of(self.env().caller())) >= value ==> result.is_ok())]
        #[ensures(old(self.balance_of(self.env().caller())) < value ==> result === Err(Error::InsufficientBalance))]
        pub fn transfer(&mut self, to: AccountId, value: Balance) -> Result<()> {
            // Cannot chain pure functions :(
            let from = self.env.caller();
            self.transfer_from_to(&from, &to, value)
        }

        /// Allows `spender` to withdraw from the caller's account multiple times, up to
        /// the `value` amount.
        ///
        /// If this function is called again it overwrites the current allowance with
        /// `value`.
        ///
        /// An `Approval` event is emitted.
        #[requires(
            resource(
                Allowance(self.env().caller(), spender),
                self.allowance_impl(&self.env().caller(), &spender)
            )
        )]
        #[ensures(
            resource(
                Allowance(old(self.env().caller()), spender),
                value
            )
        )]
        #[ensures(result.is_ok())]
        pub fn approve(&mut self, spender: AccountId, value: Balance) -> Result<()> {
            consume!(resource(
                Allowance(self.env().caller(), spender),
                self.allowance_impl(&self.env().caller(), &spender)
            ));
            produce!(resource(Allowance(self.env().caller(), spender), value));

            // Cannot chain pure functions :(
            // let owner = self.env().caller();
            self.allowances.insert(&(self.env.caller(), spender), &value);
            prusti_assert!(self.env().caller() == old(self.env().caller()));
            // self.env().emit_event(Approval {
            //     owner,
            //     spender,
            //     value,
            // })
            Ok(())
        }

        /// Transfers `value` tokens on the behalf of `from` to the account `to`.
        ///
        /// This can be used to allow a contract to transfer tokens on ones behalf and/or
        /// to charge fees in sub-currencies, for example.
        ///
        /// On success a `Transfer` event is emitted.
        ///
        /// # Errors
        ///
        /// Returns `InsufficientAllowance` error if there are not enough tokens allowed
        /// for the caller to withdraw from `from`.
        ///
        /// Returns `InsufficientBalance` error if there are not enough tokens on
        /// the account balance of `from`.
        // #[requires(self.allowance_impl(from, &self.env().caller()) >= value)]
        #[requires(
            (self.allowance_impl(&from, &self.env.caller()) >= value &&
            self.balance_of(from) >= value) ==> resource(Money(from), value)
        )]
        #[requires(
            (self.allowance_impl(&from, &self.env.caller()) >= value &&
            self.balance_of(from) >= value) ==> resource(Allowance(from, self.env().caller()), value)
        )]
        #[ensures(
            (old(self.allowance_impl(&from, &self.env.caller()) >= value) &&
             old(self.balance_of(from) >= value)) ==> resource(Money(to), value))]
        #[ensures(
            old(self.allowance_impl(&from, &self.env.caller())) < value ==>
            result === Err(Error::InsufficientAllowance))]
        pub fn transfer_from(
            &mut self,
            from: AccountId,
            to: AccountId,
            value: Balance,
        ) -> Result<()> {
            // Cannot chain pure functions :(
            let caller = self.env.caller();
            let allowance = self.allowance_impl(&from, &caller);
            if allowance < value {
                return Err(Error::InsufficientAllowance);
            }
            // .? Op is not supported
            let result = self.transfer_from_to(&from, &to, value);
            if result.is_err() {
                return result;
            }
            self.allowances
                .insert(&(from, caller), &(allowance - value));
            consume!(resource(Allowance(from, caller), value));
            Ok(())
        }

        /// Transfers `value` amount of tokens from the caller's account to account `to`.
        ///
        /// On success a `Transfer` event is emitted.
        ///
        /// # Errors
        ///
        /// Returns `InsufficientBalance` error if there are not enough tokens on
        /// the caller's account balance.
        #[requires(self.balance_of(*from) >= value ==> resource(Money(*from), value))]
        #[ensures(old(self.balance_of(*from) >= value) ==> resource(Money(*to), value))]
        #[ensures(old(self.balance_of(*from)) >= value ==> result.is_ok())]
        #[ensures(old(self.balance_of(*from)) < value ==> result === Err(Error::InsufficientBalance))]
        fn transfer_from_to(
            &mut self,
            from: &AccountId,
            to: &AccountId,
            value: Balance,
        ) -> Result<()> {
            let from_balance = self.balance_of_impl(from);
            if from_balance < value {
                return Err(Error::InsufficientBalance);
            }

            self.balances.insert(from, &(from_balance - value));
            // prusti_assert!(self.balances.get(from) === Some(from_balance - value));
            // prusti_assert!(self.balance_of_impl(from) === from_balance - value);
            let to_balance = self.balance_of_impl(to);
            self.balances.insert(to, &(to_balance + value));
            produce!(resource(Money(*to), value));
            // self.env().emit_event(Transfer {
            //     from: Some(*from),
            //     to: Some(*to),
            //     value,
            // });
            Ok(())
        }
    }

    // TESTS

    /// Get the actual balance of an account.
    fn balance_of_works() {
        let alice = 0;
        let bob = 1;
        // Constructor works
        let erc20 = Erc20::new(100, alice);
        // Alice owns all the tokens on contract instantiation
        prusti_assert!(erc20.balance_of(alice) == 100);
        prusti_assert!(erc20.balance_of(bob) == 0);
    }

    fn transfer_works() {
        let alice = 0;
        let bob = 1;
        // Constructor works.
        let mut erc20 = Erc20::new(100, alice);
        // Transfer event triggered during initial construction.

        prusti_assume!(erc20.env().caller() == alice);
        prusti_assert_eq!(erc20.balance_of(bob), 0);
        // Alice transfers 10 tokens to Bob.
        let transfer_result = erc20.transfer(bob, 10);
        prusti_assert!(transfer_result.is_ok());
        // Bob owns 10 tokens.
        prusti_assert_eq!(erc20.balance_of(bob), 10);

        // let emitted_events = ink::env::test::recorded_events().collect::<Vec<_>>();
        // assert_eq!(emitted_events.len(), 2);
    }

    fn invalid_transfer_should_fail() {
        let alice = 0;
        let bob = 1;
        let eve = 5;
        // Constructor works.
        let mut erc20 = Erc20::new(100, alice);

        prusti_assert_eq!(erc20.balance_of(bob), 0);

        prusti_assume!(erc20.env().caller() == bob);

        let transfer_result = erc20.transfer(eve, 10);

        // Bob fails to transfers 10 tokens to Eve.
        prusti_assert_eq!(transfer_result, Err(Error::InsufficientBalance));
        // Alice owns all the tokens.
        prusti_assert_eq!(erc20.balance_of(alice), 100);
        prusti_assert_eq!(erc20.balance_of(bob), 0);
        prusti_assert_eq!(erc20.balance_of(eve), 0);

        // Transfer event triggered during initial construction.
        // let emitted_events = ink::env::test::recorded_events().collect::<Vec<_>>();
        // assert_eq!(emitted_events.len(), 1);
        // assert_transfer_event(
        //     &emitted_events[0],
        //     None,
        //     Some(AccountId::from([0x01; 32])),
        //     100,
        // );
    }

    fn transfer_from_works() {
        let alice = 0;
        let bob = 1;
        let eve = 5;

        // Constructor works.
        let mut erc20 = Erc20::new(100, alice);
        prusti_assert!(erc20.allowance_impl(&alice, &bob) == 0);
        prusti_assume!(erc20.env().caller() == alice);
        prusti_assert_eq!(erc20.allowance_impl(&alice, &alice), 0);
        let transfer_result = erc20.transfer_from(alice, eve, 10);
        // prusti_assert_eq!(
        //     transfer_result,
        //     Err(Error::InsufficientAllowance)
        // );

        prusti_assume!(erc20.env().caller() == alice);
        // Alice approves Bob for token transfers on her behalf.
        prusti_assert!(erc20.allowance_impl(&alice, &bob) == 0);
        let approve_result = erc20.approve(bob, 10);
        prusti_assert_eq!(approve_result, Ok(()));

        prusti_assume!(erc20.env().caller() == bob);
        // Bob transfers tokens from Alice to Eve.
        let transfer_result = erc20.transfer_from(alice, eve, 10);
        prusti_assert_eq!(transfer_result, Ok(()));
        // Eve owns tokens.
        prusti_assert_eq!(erc20.balance_of(eve), 10);

        // // Check all transfer events that happened during the previous calls:
        // let emitted_events = ink::env::test::recorded_events().collect::<Vec<_>>();
        // assert_eq!(emitted_events.len(), 3);
        // assert_transfer_event(
        //     &emitted_events[0],
        //     None,
        //     Some(AccountId::from([0x01; 32])),
        //     100,
        // );
        // // The second event `emitted_events[1]` is an Approve event that we skip
        // // checking.
        // assert_transfer_event(
        //     &emitted_events[2],
        //     Some(AccountId::from([0x01; 32])),
        //     Some(AccountId::from([0x05; 32])),
        //     10,
        // );
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        use ink::primitives::{Clear, Hash};

        type Event = <Erc20 as ::ink::reflect::ContractEventBase>::Type;

        #[ink::test]
        fn allowance_must_not_change_on_failed_transfer() {
            let mut erc20 = Erc20::new(100);
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();

            // Alice approves Bob for token transfers on her behalf.
            let alice_balance = erc20.balance_of(accounts.alice);
            let initial_allowance = alice_balance + 2;
            assert_eq!(erc20.approve(accounts.bob, initial_allowance), Ok(()));

            // Get contract address.
            let callee = ink::env::account_id::<ink::env::DefaultEnvironment>();
            ink::env::test::set_callee::<ink::env::DefaultEnvironment>(callee);
            ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.bob);

            // Bob tries to transfer tokens from Alice to Eve.
            let emitted_events_before = ink::env::test::recorded_events().count();
            assert_eq!(
                erc20.transfer_from(accounts.alice, accounts.eve, alice_balance + 1),
                Err(Error::InsufficientBalance)
            );
            // Allowance must have stayed the same
            assert_eq!(
                erc20.allowance(accounts.alice, accounts.bob),
                initial_allowance
            );
            // No more events must have been emitted
            assert_eq!(
                emitted_events_before,
                ink::env::test::recorded_events().count()
            )
        }

        /// For calculating the event topic hash.
        struct PrefixedValue<'a, 'b, T> {
            pub prefix: &'a [u8],
            pub value: &'b T,
        }

        impl<X> scale::Encode for PrefixedValue<'_, '_, X>
        where
            X: scale::Encode,
        {
            #[inline]
            fn size_hint(&self) -> usize {
                self.prefix.size_hint() + self.value.size_hint()
            }

            #[inline]
            fn encode_to<T: scale::Output + ?Sized>(&self, dest: &mut T) {
                self.prefix.encode_to(dest);
                self.value.encode_to(dest);
            }
        }

        fn encoded_into_hash<T>(entity: &T) -> Hash
        where
            T: scale::Encode,
        {
            use ink::{
                env::hash::{Blake2x256, CryptoHash, HashOutput},
                primitives::Clear,
            };

            let mut result = Hash::CLEAR_HASH;
            let len_result = result.as_ref().len();
            let encoded = entity.encode();
            let len_encoded = encoded.len();
            if len_encoded <= len_result {
                result.as_mut()[..len_encoded].copy_from_slice(&encoded);
                return result;
            }
            let mut hash_output =
                <<Blake2x256 as HashOutput>::Type as Default>::default();
            <Blake2x256 as CryptoHash>::hash(&encoded, &mut hash_output);
            let copy_len = core::cmp::min(hash_output.len(), len_result);
            result.as_mut()[0..copy_len].copy_from_slice(&hash_output[0..copy_len]);
            result
        }
    }

    #[cfg(all(test, feature = "e2e-tests"))]
    mod e2e_tests {
        use super::*;
        use ink_e2e::build_message;
        type E2EResult<T> = std::result::Result<T, Box<dyn std::error::Error>>;

        #[ink_e2e::test]
        async fn e2e_transfer(mut client: ink_e2e::Client<C, E>) -> E2EResult<()> {
            // given
            let total_supply = 1_000_000_000;
            let constructor = Erc20Ref::new(total_supply);
            let contract_acc_id = client
                .instantiate("erc20", &ink_e2e::alice(), constructor, 0, None)
                .await
                .expect("instantiate failed")
                .account_id;

            // when
            let total_supply_msg = build_message::<Erc20Ref>(contract_acc_id.clone())
                .call(|erc20| erc20.total_supply());
            let total_supply_res = client
                .call_dry_run(&ink_e2e::bob(), &total_supply_msg, 0, None)
                .await;

            let bob_account = ink_e2e::account_id(ink_e2e::AccountKeyring::Bob);
            let transfer_to_bob = 500_000_000u128;
            let transfer = build_message::<Erc20Ref>(contract_acc_id.clone())
                .call(|erc20| erc20.transfer(bob_account.clone(), transfer_to_bob));
            let _transfer_res = client
                .call(&ink_e2e::alice(), transfer, 0, None)
                .await
                .expect("transfer failed");

            let balance_of = build_message::<Erc20Ref>(contract_acc_id.clone())
                .call(|erc20| erc20.balance_of(bob_account));
            let balance_of_res = client
                .call_dry_run(&ink_e2e::alice(), &balance_of, 0, None)
                .await;

            // then
            assert_eq!(
                total_supply,
                total_supply_res.return_value(),
                "total_supply"
            );
            assert_eq!(transfer_to_bob, balance_of_res.return_value(), "balance_of");

            Ok(())
        }

        #[ink_e2e::test]
        async fn e2e_allowances(mut client: ink_e2e::Client<C, E>) -> E2EResult<()> {
            // given
            let total_supply = 1_000_000_000;
            let constructor = Erc20Ref::new(total_supply);
            let contract_acc_id = client
                .instantiate("erc20", &ink_e2e::bob(), constructor, 0, None)
                .await
                .expect("instantiate failed")
                .account_id;

            // when

            let bob_account = ink_e2e::account_id(ink_e2e::AccountKeyring::Bob);
            let charlie_account = ink_e2e::account_id(ink_e2e::AccountKeyring::Charlie);

            let amount = 500_000_000u128;
            let transfer_from =
                build_message::<Erc20Ref>(contract_acc_id.clone()).call(|erc20| {
                    erc20.transfer_from(
                        bob_account.clone(),
                        charlie_account.clone(),
                        amount,
                    )
                });
            let transfer_from_result = client
                .call(&ink_e2e::charlie(), transfer_from, 0, None)
                .await;

            assert!(
                transfer_from_result.is_err(),
                "unapproved transfer_from should fail"
            );

            // Bob approves Charlie to transfer up to amount on his behalf
            let approved_value = 1_000u128;
            let approve_call = build_message::<Erc20Ref>(contract_acc_id.clone())
                .call(|erc20| erc20.approve(charlie_account.clone(), approved_value));
            client
                .call(&ink_e2e::bob(), approve_call, 0, None)
                .await
                .expect("approve failed");

            // `transfer_from` the approved amount
            let transfer_from =
                build_message::<Erc20Ref>(contract_acc_id.clone()).call(|erc20| {
                    erc20.transfer_from(
                        bob_account.clone(),
                        charlie_account.clone(),
                        approved_value,
                    )
                });
            let transfer_from_result = client
                .call(&ink_e2e::charlie(), transfer_from, 0, None)
                .await;
            assert!(
                transfer_from_result.is_ok(),
                "approved transfer_from should succeed"
            );

            let balance_of = build_message::<Erc20Ref>(contract_acc_id.clone())
                .call(|erc20| erc20.balance_of(bob_account));
            let balance_of_res = client
                .call_dry_run(&ink_e2e::alice(), &balance_of, 0, None)
                .await;

            // `transfer_from` again, this time exceeding the approved amount
            let transfer_from =
                build_message::<Erc20Ref>(contract_acc_id.clone()).call(|erc20| {
                    erc20.transfer_from(bob_account.clone(), charlie_account.clone(), 1)
                });
            let transfer_from_result = client
                .call(&ink_e2e::charlie(), transfer_from, 0, None)
                .await;
            assert!(
                transfer_from_result.is_err(),
                "transfer_from exceeding the approved amount should fail"
            );

            assert_eq!(
                total_supply - approved_value,
                balance_of_res.return_value(),
                "balance_of"
            );

            Ok(())
        }
    }
}

fn main() {}
