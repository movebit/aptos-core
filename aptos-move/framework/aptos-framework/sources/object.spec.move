spec aptos_framework::object {

    spec module {
        pragma verify = false;
        pragma aborts_if_is_strict;
    }

    spec exists_at<T: key>(object: address): bool {
        pragma verify = false;
    }

    spec address_to_object<T: key>(object: address): Object<T> {
        pragma verify = false;
    }

    spec is_object(object: address): bool {
        pragma verify = true;
    }

    spec create_object_address(source: &address, seed: vector<u8>): address {
        pragma opaque;
        pragma aborts_if_is_strict = false;
        aborts_if [abstract] false;
        ensures [abstract] result == spec_create_object_address(source, seed);
    }

    spec create_user_derived_object_address(source: address, derive_from: address): address {
        pragma opaque;
        pragma aborts_if_is_strict = false;
        aborts_if [abstract] false;
        ensures [abstract] result == spec_create_user_derived_object_address(source, derive_from);
    }

   
    spec create_guid_object_address(source: address, creation_num: u64): address {
        pragma opaque;
        pragma aborts_if_is_strict = false;
        aborts_if [abstract] false;
        ensures [abstract] result == spec_create_guid_object_address(source, creation_num);
    }

    spec object_address<T: key>(object: &Object<T>): address {
        pragma verify = true;
    }

    spec convert<X: key, Y: key>(object: Object<X>): Object<Y> {
        pragma verify = false;
        //TODO: involved with native
    }

    spec create_named_object(creator: &signer, seed: vector<u8>): ConstructorRef {
        pragma verify = true;
        let creator_address = signer::address_of(creator);
        let obj_addr = spec_create_object_address(creator_address, seed);
        aborts_if exists<ObjectCore>(obj_addr);
    }

    spec create_user_derived_object(creator_address: address, derive_ref: &DeriveRef): ConstructorRef {
        pragma verify = true;
        let obj_addr = spec_create_user_derived_object_address(creator_address, derive_ref.self);
        aborts_if exists<ObjectCore>(obj_addr);
    }

    spec create_object_from_account(creator: &signer): ConstructorRef {
        pragma verify = true;
        aborts_if !exists<account::Account>(signer::address_of(creator));
        //Guid properties
        let object_data = global<account::Account>(signer::address_of(creator));
        aborts_if object_data.guid_creation_num + 1 > MAX_U64;
        aborts_if object_data.guid_creation_num + 1 >= account::MAX_GUID_CREATION_NUM;
    }

    spec create_object_from_object(creator: &signer): ConstructorRef{
        pragma verify = true;
        aborts_if !exists<ObjectCore>(signer::address_of(creator));
        //Guid properties
        let object_data = global<ObjectCore>(signer::address_of(creator));
        aborts_if object_data.guid_creation_num + 1 > MAX_U64;
    }

    spec create_object_from_guid(creator_address: address, guid: guid::GUID): ConstructorRef {
        pragma verify = true;
        //TODO: We assume the sha3_256 is reachable
    }

    spec create_object_internal(
        creator_address: address,
        object: address,
        can_delete: bool,
    ): ConstructorRef {
        pragma verify = true;
        aborts_if exists<ObjectCore>(object);
    }

    spec generate_delete_ref(ref: &ConstructorRef): DeleteRef {
        pragma verify = true;
        aborts_if !ref.can_delete;
    }

    spec disable_ungated_transfer(ref: &TransferRef) {
        pragma verify = true;
        aborts_if !exists<ObjectCore>(ref.self);
    }

    spec generate_extend_ref(ref: &ConstructorRef): ExtendRef {
        pragma verify = true;
    }

    spec generate_transfer_ref(ref: &ConstructorRef): TransferRef {
        pragma verify = true;
    }

    spec generate_derive_ref(ref: &ConstructorRef): DeriveRef {
        pragma verify = true;
    }

    spec generate_signer(ref: &ConstructorRef): signer {
        pragma verify = true;
    }

    spec address_from_constructor_ref(ref: &ConstructorRef): address {
        pragma verify = true;
    }

    spec object_from_constructor_ref<T: key>(ref: &ConstructorRef): Object<T> {
        pragma verify = false;
        //TODO: Involved native fun
    }

    spec can_generate_delete_ref(ref: &ConstructorRef): bool {
        pragma verify = true;
    }

    // Signer required functions

    spec create_guid(object: &signer): guid::GUID{
        pragma verify = true;
        aborts_if !exists<ObjectCore>(signer::address_of(object));
        //Guid properties
        let object_data = global<ObjectCore>(signer::address_of(object));
        aborts_if object_data.guid_creation_num + 1 > MAX_U64;
    }

    spec new_event_handle<T: drop + store>(
        object: &signer,
    ): event::EventHandle<T>{
        pragma verify = true;
        aborts_if !exists<ObjectCore>(signer::address_of(object));
        //Guid properties
        let object_data = global<ObjectCore>(signer::address_of(object));
        aborts_if object_data.guid_creation_num + 1 > MAX_U64;
    }

    spec address_from_delete_ref(ref: &DeleteRef): address {
        pragma verify = true;
    }

    spec object_from_delete_ref<T: key>(ref: &DeleteRef): Object<T> {
        pragma verify = false;
        //TODO: Involved native fun
    }

    spec delete(ref: DeleteRef) {
        pragma verify = true;
        aborts_if !exists<ObjectCore>(ref.self);
    }

    spec generate_signer_for_extending(ref: &ExtendRef): signer {
        pragma verify = true;
    }

    spec address_from_extend_ref(ref: &ExtendRef): address {
        pragma verify = true;
    }

    spec enable_ungated_transfer(ref: &TransferRef) {
        pragma verify = true;
        aborts_if !exists<ObjectCore>(ref.self);
    }

    spec transfer_with_ref(ref: LinearTransferRef, to: address){
        pragma verify = true;
        let object = global<ObjectCore>(ref.self);
        aborts_if !exists<ObjectCore>(ref.self);
        aborts_if object.owner != ref.owner;
    }

    spec transfer_call(
        owner: &signer,
        object: address,
        to: address,
    ) {
        pragma verify = true;
        let owner_address = signer::address_of(owner);
        aborts_if !exists<ObjectCore>(object);
        aborts_if !global<ObjectCore>(object).allow_ungated_transfer;
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object && !exists<ObjectCore>(object);
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object && !global<ObjectCore>(object).allow_ungated_transfer;
    }

    spec transfer<T: key>(
        owner: &signer,
        object: Object<T>,
        to: address,
    ) {
        pragma verify = true;
        let owner_address = signer::address_of(owner);
        let object_address = object.inner;
        aborts_if !exists<ObjectCore>(object_address);
        aborts_if !global<ObjectCore>(object_address).allow_ungated_transfer;
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object_address && !exists<ObjectCore>(object_address);
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object_address && !global<ObjectCore>(object_address).allow_ungated_transfer;
    }

    spec transfer_raw(
        owner: &signer,
        object: address,
        to: address,
    ) {
        pragma verify = true;
        let owner_address = signer::address_of(owner);
        aborts_if !exists<ObjectCore>(object);
        aborts_if !global<ObjectCore>(object).allow_ungated_transfer;
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object && !exists<ObjectCore>(object);
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object && !global<ObjectCore>(object).allow_ungated_transfer;
    }

    spec transfer_to_object<O: key, T: key> (
        owner: &signer,
        object: Object<O>,
        to: Object<T>,
    ){
        pragma verify = true;
        let owner_address = signer::address_of(owner);
        let object_address = object.inner;
        aborts_if !exists<ObjectCore>(object_address);
        aborts_if !global<ObjectCore>(object_address).allow_ungated_transfer;
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object_address && !exists<ObjectCore>(object_address);
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner_address != object_address && !global<ObjectCore>(object_address).allow_ungated_transfer;
    }

    spec verify_ungated_and_descendant(owner: address, destination: address) {
        pragma verify = true;
        aborts_if !exists<ObjectCore>(destination);
        aborts_if !global<ObjectCore>(destination).allow_ungated_transfer;
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner != destination && !exists<ObjectCore>(destination);
        aborts_if exists i in 0 .. MAXIMUM_OBJECT_NESTING-1:
            owner != destination && !global<ObjectCore>(destination).allow_ungated_transfer;
    }

    spec ungated_transfer_allowed<T: key>(object: Object<T>): bool {
        pragma verify = true;
        aborts_if !exists<ObjectCore>(object.inner);
    }

    spec owner<T: key>(object: Object<T>): address{
        pragma verify = true;
        aborts_if !exists<ObjectCore>(object.inner);
    }

    spec owns<T: key>(object: Object<T>, owner: address): bool {
        pragma verify = true;
        aborts_if object.inner != owner && !exists<ObjectCore>(object.inner);
    }

    // Helper function
    spec fun spec_create_object_address(source: address, seed: vector<u8>): address;
    
    spec fun spec_create_user_derived_object_address(source: address, derive_from: address): address;
    
    spec fun spec_create_guid_object_address(source: address, creation_num: u64): address;

}
