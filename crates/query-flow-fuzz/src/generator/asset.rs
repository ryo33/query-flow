//! Synthetic asset implementation.

use super::NodeId;
use query_flow::{AssetKey, DurabilityLevel};
use rand::Rng;
use serde::{Deserialize, Serialize};

/// Synthetic asset key for testing.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyntheticAssetKey(pub NodeId);

impl AssetKey for SyntheticAssetKey {
    type Asset = Vec<u8>;

    fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool {
        old == new
    }

    fn durability(&self) -> DurabilityLevel {
        DurabilityLevel::Stable
    }
}

impl std::fmt::Display for SyntheticAssetKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Asset({})", self.0 .0)
    }
}

/// Generate synthetic asset data.
///
/// The data includes the node ID and version for determinism,
/// followed by random bytes to fill the requested size.
pub fn generate_asset_data<R: Rng>(
    node_id: NodeId,
    size: usize,
    version: u64,
    rng: &mut R,
) -> Vec<u8> {
    let mut data = Vec::with_capacity(size);

    // Include node ID and version for determinism
    data.extend_from_slice(&node_id.0.to_le_bytes());
    data.extend_from_slice(&version.to_le_bytes());

    // Fill rest with pseudo-random data based on seed
    // Use a simple LCG seeded by node_id and version for reproducibility
    let mut seed = (node_id.0 as u64) ^ (version.wrapping_mul(0x9E3779B97F4A7C15));
    while data.len() < size {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        data.push((seed >> 56) as u8);
    }
    data.truncate(size);

    // Add some actual randomness if RNG is provided
    if data.len() > 12 {
        let random_byte: u8 = rng.gen();
        data[12] = random_byte;
    }

    data
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_asset_data() {
        let mut rng = rand::thread_rng();
        let data = generate_asset_data(NodeId(42), 64, 1, &mut rng);
        assert_eq!(data.len(), 64);

        // First bytes should contain node_id
        let node_id = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        assert_eq!(node_id, 42);
    }

    #[test]
    fn test_different_versions_produce_different_data() {
        let mut rng = rand::thread_rng();
        let data1 = generate_asset_data(NodeId(1), 32, 1, &mut rng);
        let data2 = generate_asset_data(NodeId(1), 32, 2, &mut rng);
        assert_ne!(data1, data2);
    }
}
