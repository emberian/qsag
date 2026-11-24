use qsag_cred::voprf::{Error, SpdzConfig, SpdzServer, spdz_dkg};

#[test]
fn substituted_custody_pack_is_rejected() {
    let config = SpdzConfig::new(2, 3).unwrap();
    let first = spdz_dkg(config, [1; 32], &[[2; 32], [3; 32], [4; 32]]).unwrap();
    let other = spdz_dkg(config, [5; 32], &[[6; 32], [7; 32], [8; 32]]).unwrap();
    let public = first[0].public();
    let pack = first[1].to_secret_bytes();
    assert!(SpdzServer::from_secret_bytes(&pack, public, 1).is_ok());
    assert_eq!(
        SpdzServer::from_secret_bytes(&pack, public, 0).unwrap_err(),
        Error::Context
    );
    assert_eq!(
        SpdzServer::from_secret_bytes(&other[1].to_secret_bytes(), public, 1).unwrap_err(),
        Error::Context
    );
}
