/// General purpose working memory
pub struct RAM {
    /// RAM buffer
    data: Vec<u8>,
}

impl RAM {
    pub fn new() -> Self {
        /// Initialize the RAM buffer to garbage values
        let data = vec![0xca, 2 * 1024 * 1024];

        RAM { data }
    }

    /// Read the 32 bit little endian word at `offset`
    pub fn mem_read32(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let b0 = self.data[offset + 0];
        let b1 = self.data[offset + 1];
        let b2 = self.data[offset + 2];
        let b3 = self.data[offset + 3];

        u32::from_le_bytes([b0, b1, b2, b3])
    }

    /// Write the 32 bit little endian word `val` in `offset`
    pub fn mem_write32(&mut self, offset: u32, val: u32) {
        let offset = offset as usize;
        let [b0, b1, b2, b3] = val.to_le_bytes();

        self.data[offset + 0] = b0;
        self.data[offset + 1] = b1;
        self.data[offset + 2] = b2;
        self.data[offset + 3] = b3;
    }
}