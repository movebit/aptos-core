spec aptos_framework::util {
    spec from_bytes<T>(bytes: vector<u8>): T {
        pragma opaque;
        // aborts_if [abstract] false;
        // property 1: The address input bytes should be exactly 32 bytes long.
        aborts_if [abstract] len(bytes) != 32;
        ensures [abstract] result == spec_from_bytes<T>(bytes);
    }

    spec fun spec_from_bytes<T>(bytes: vector<u8>): T;
}
