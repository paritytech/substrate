#![cfg_attr(not(feature = "std"), no_std)]

use ibc::core::ics04_channel::msgs::acknowledgement::Acknowledgement;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use frame_support::weights::Weight;

/// Callback Weight
/// This trait must be implemented by module callback handlers to be able to estimate the weight
/// of the callback function.
pub trait CallbackWeight {
    /// Returns the callback weight for the channel open init ibc message
    fn on_chan_open_init(&self) -> Weight;

    /// Returns the callback weight for the channel open try ibc message
    fn on_chan_open_try(&self) -> Weight;

    /// Returns the callback weight for the channel open acknowledgement ibc message
    fn on_chan_open_ack(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight;

    /// Returns the callback weight for the channel open confirm ibc message
    fn on_chan_open_confirm(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight;

    /// Returns the callback weight for the channel close init ibc message
    fn on_chan_close_init(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight;

    /// Returns the callback weight for the channel close confirm ibc message
    fn on_chan_close_confirm(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight;

    /// Returns the callback weight for the receive packet ibc message
    fn on_recv_packet(&self, _packet: &Packet) -> Weight;

    /// Returns the callback weight for the packet acknowledgement ibc message
    fn on_acknowledgement_packet(
        &self,
        _packet: &Packet,
        _acknowledgement: &Acknowledgement,
    ) -> Weight;

    /// Returns the callback weight for the packet timeout ibc message
    fn on_timeout_packet(&self, packet: &Packet) -> Weight;
}

impl CallbackWeight for () {
    fn on_chan_open_init(&self) -> Weight {
        Weight::MAX
    }

    fn on_chan_open_try(&self) -> Weight {
        Weight::MAX
    }

    fn on_chan_open_ack(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight {
        Weight::MAX
    }

    fn on_chan_open_confirm(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight {
        Weight::MAX
    }

    fn on_chan_close_init(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight {
        Weight::MAX
    }

    fn on_chan_close_confirm(&self, _port_id: &PortId, _channel_id: &ChannelId) -> Weight {
        Weight::MAX
    }

    fn on_recv_packet(&self, _packet: &Packet) -> Weight {
        Weight::MAX
    }

    fn on_acknowledgement_packet(
        &self,
        _packet: &Packet,
        _acknowledgement: &Acknowledgement,
    ) -> Weight {
        Weight::MAX
    }

    fn on_timeout_packet(&self, _packet: &Packet) -> Weight {
        Weight::MAX
    }
}
